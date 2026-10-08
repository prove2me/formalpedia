-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_expected_decrease
-- name    : NesterovRCD.Sublinear.expected_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:56.904841+00:00
-- url     : https://prove2.me/theorems/a9488547-21c9-4448-ab10-9cdda9a75b32
-- title:
--   (2.13) — $f(x)-\sum_ip_\alpha^{(i)}f(T_i(x))\ge\frac1{2S_\alpha}(\|\nabla f(x)\|^*_{1-\alpha})^2$
-- statement:
--   Let $n\ge1$, let $f$ satisfy (2.2) with constants $L_i>0$ on finite-dimensional normed blocks, let $\alpha\in\mathbb R$, and let $p_\alpha^{(i)}=L_i^\alpha/S_\alpha$ be the probabilities (2.5). For an arbitrary choice of the vectors $s^\#$, every point $x$ satisfies
--   $$f(x)-\sum_{i=1}^np_\alpha^{(i)}f(T_i(x))\ge\frac1{2S_\alpha}\big(\|\nabla f(x)\|^*_{1-\alpha}\big)^2 .$$
--
--   The left side is the expected decrease $f(x_k)-E_{i_k}f(x_{k+1})$ of one iteration of RCDM$(\alpha,x_0)$ at $x_k=x$; the right side expresses it through the full gradient in the dual weighted norm.
--
--   **Formalization Note** The statement is pointwise in $x$, which is how the paper uses it for the random iterate $x_k$. $n\ge1$ is explicit (for $n=0$ the probabilities are $0/0$). Convexity is not needed.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 7, proof of Theorem 1, (2.13)

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.Sublinear

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem expected_decrease (hn : 0 < n) (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (α : ℝ) (x : Blocks E) :
    wdual L (1 - α) (gradBlocks f x) ^ 2 / (2 * S L α)
      ≤ f x - ∑ i, prob L α i * f (coordStep f L sharp i x) := by sorry

end NesterovRCD.Sublinear
