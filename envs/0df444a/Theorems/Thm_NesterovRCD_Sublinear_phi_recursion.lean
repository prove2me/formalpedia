-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_phi_recursion
-- name    : NesterovRCD.Sublinear.phi_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:46.816515+00:00
-- url     : https://prove2.me/theorems/d2e9b4f3-fee6-415a-adbf-d320b79a6a73
-- title:
--   Proof of Theorem 1 — $\varphi_k-\varphi_{k+1}\ge\frac1C(\varphi_k-f^*)^2$, $C=2S_\alpha R^2_{1-\alpha}(x_0)$
-- statement:
--   Let $n\ge1$ and let $f:\mathbb R^N\to\mathbb R$ be convex and satisfy (2.2) with constants $L_i>0$ on finite-dimensional normed blocks. Fix $\alpha\in\mathbb R$, a starting point $x_0$, an arbitrary choice of the vectors $s^\#$, and a minimizer $x_*$ of $f$ with $f^*=f(x_*)$. Let $R\ge R_{1-\alpha}(x_0)$, i.e. $\|x-x'_*\|_{1-\alpha}\le R$ whenever $f(x)\le f(x_0)$ and $x'_*$ is a minimizer. Let $\varphi_k=E_{\xi_{k-1}}f(x_k)$ be the expected value of the $k$-th iterate of RCDM$(\alpha,x_0)$ over the draws $i_0,\dots,i_{k-1}$. Then with $C=2S_\alpha R^2$, for every $k\ge0$,
--   $$(\varphi_k-f^*)^2\le C\,(\varphi_k-\varphi_{k+1}) .$$
--
--   This is the recursion from which Theorem 1 follows by summing $\frac1{\varphi_{k+1}-f^*}-\frac1{\varphi_k-f^*}\ge\frac1C$.
--
--   **Formalization Note** The paper writes $\varphi_k-\varphi_{k+1}\ge\frac1C(\varphi_k-f^*)^2$; we state it multiplied by $C$, which is equivalent for $C>0$ and stays meaningful when $R=0$. $R_{1-\alpha}(x_0)$ is replaced by an upper bound $R$ (see the definition item). $\varphi_k$ is the finite sum over all index sequences $(i_0,\dots,i_{k-1})\in\{1,\dots,n\}^k$ weighted by $\prod_sp_\alpha^{(i_s)}$. Convexity and $X_*\neq\emptyset$ are the standing assumptions of §2; boundedness of $X_*$ is implied by the existence of $R$.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 7, proof of Theorem 1, after (2.13)

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.Sublinear

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem phi_recursion (hn : 0 < n) (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (α : ℝ) (x0 xs : Blocks E) (hxs : IsMinimizer f xs)
    (R : ℝ) (hR : LevelRadiusLE f L (1 - α) x0 R) (k : ℕ) :
    (expect (prob L α) k (fun idx => f (rcdm f L sharp x0 k idx)) - f xs) ^ 2
      ≤ 2 * S L α * R ^ 2 *
        (expect (prob L α) k (fun idx => f (rcdm f L sharp x0 k idx))
          - expect (prob L α) (k + 1) (fun idx => f (rcdm f L sharp x0 (k + 1) idx))) := by sorry

end NesterovRCD.Sublinear
