-- Prove2me | Theorems.Thm_GoldenRatioVI_eq_5_norm_sq_combination
-- name    : GoldenRatioVI.eq_5_norm_sq_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:23:55.885522+00:00
-- url     : https://prove2.me/theorems/225105ac-a0c6-4ce9-ad22-418d5556518e
-- title:
--   Eq. (5): $\|\alpha a+(1-\alpha)b\|^2$ identity
-- statement:
--   Let $\mathcal E$ be a real inner product space. For all $a,b\in\mathcal E$ and all $\alpha\in\mathbb R$,
--   $$\|\alpha a+(1-\alpha)b\|^2=\alpha\|a\|^2+(1-\alpha)\|b\|^2-\alpha(1-\alpha)\|a-b\|^2 .$$
--
--   The identity is applied with $\alpha=\varphi/(\varphi-1)$ to obtain (24).
--
--   Differences from the source:
--   - generalization: E a finite-dimensional vector space with inner product → any real inner product space; reason: the identity is algebraic; the finite-dimensional case is a special case
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), Preliminaries, p. 3, eq. (5)

import Mathlib

namespace GoldenRatioVI

/-- **Identity (5).**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), Preliminaries, p. 3, eq. (5):
"‖αa + (1 − α)b‖² = α‖a‖² + (1 − α)‖b‖² − α(1 − α)‖a − b‖² ∀a, b ∈ E ∀α ∈ R."

**Formalization Note.** Stated in every real inner product space; the paper's `E` is
finite-dimensional, a special case. -/
theorem eq_5_norm_sq_combination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (α : ℝ) :
    ‖α • a + (1 - α) • b‖ ^ 2 =
      α * ‖a‖ ^ 2 + (1 - α) * ‖b‖ ^ 2 - α * (1 - α) * ‖a - b‖ ^ 2 := by sorry

end GoldenRatioVI
