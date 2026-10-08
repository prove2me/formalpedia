-- Prove2me | Theorems.Thm_NesterovRCD_HighProb_fReg_constants
-- name    : NesterovRCD.HighProb.fReg_constants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:26.700912+00:00
-- url     : https://prove2.me/theorems/02e52d0c-7f6f-4993-a322-205750412c9f
-- title:
--   §3, p. 11 — $f_\mu$ is $\mu$-strongly convex in $\|\cdot\|_0$, has block constants $L_i+\mu$, and $L(f_\mu)=S_1(f)+\mu$
-- statement:
--   Let the blocks $\mathbb R^{n_i}$ carry Euclidean norms $\|h^{(i)}\|_{(i)}^2=\langle B_ih^{(i)},h^{(i)}\rangle$ (3.4), and let $\|h\|_0^2=\sum_i\|h^{(i)}\|^2_{(i)}$ (3.9) with dual norm $\|g\|^*_0=\big[\sum_i(\|g^{(i)}\|^*_{(i)})^2\big]^{1/2}$. Let $f$ be convex with coordinate-wise Lipschitz gradient, constants $L_i>0$ (2.2), and $S_1(f)=\sum_iL_i$. For $\mu>0$ and $x_0\in\mathbb R^N$ consider the regularized objective
--   $$f_\mu(x)=f(x)+\frac\mu2\|x-x_0\|_0^2 .$$
--   Then:
--
--   1. $f_\mu$ is strongly convex with respect to $\|\cdot\|_0$ with convexity parameter $\mu$;
--   2. $f_\mu$ has a coordinate-wise Lipschitz gradient (2.2) with constants $L_i(f_\mu)=L_i(f)+\mu$, so that $S_1(f_\mu)=\sum_i[L_i(f)+\mu]=S_1(f)+n\mu$;
--   3. the gradient of $f_\mu$ is Lipschitz continuous in $\|\cdot\|_0$ with constant $L(f_\mu)=S_1(f)+\mu$: for all $x,y$,
--   $$\|\nabla f_\mu(x)-\nabla f_\mu(y)\|_0^*\le\big(S_1(f)+\mu\big)\|x-y\|_0 .$$
--
--   These are the constants with which RCDM$(1,x_0)$ is run on $f_\mu$ in Lemma 4 and Theorem 4, and with which Theorem 2 applies to $f_\mu$.
--
--   **Formalization Note** The paper's text states the three facts without a proof; the third is the meaning of "$L(f_\mu)=S_1(f)+\mu$", obtained from Lemma 2 for $\alpha=1$ (which needs $f$ convex) plus the quadratic term. Convexity of $f$ is the standing assumption of §2 and is explicit. The identity $S_1(f_\mu)=S_1(f)+n\mu$ is arithmetic once item 2 holds and is not restated. Euclidean blocks are inner-product spaces $E_i$ (with $B_i$ absorbed into the inner product); the dual norm of a block is the operator norm.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 11, §3 item 2, (3.9) and the claims on f_μ before Lemma 4

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic

namespace NesterovRCD.HighProb

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem fReg_constants (f : NesterovRCD.Sublinear.Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L) (μ : ℝ) (hμ : 0 < μ) (x0 : NesterovRCD.Sublinear.Blocks E) :
    StronglyConvexW (fReg f L μ x0) L 0 μ ∧
      NesterovRCD.Sublinear.CoordLipschitz (fReg f L μ x0) (fun i => L i + μ) ∧
      ∀ x y : NesterovRCD.Sublinear.Blocks E,
        NesterovRCD.Sublinear.wdual L 0 (fun i => NesterovRCD.Sublinear.partialGrad (fReg f L μ x0) x i - NesterovRCD.Sublinear.partialGrad (fReg f L μ x0) y i)
          ≤ (NesterovRCD.Sublinear.S L 1 + μ) * NesterovRCD.Sublinear.wnorm L 0 (x - y) := by sorry

end NesterovRCD.HighProb
