-- Prove2me | Theorems.Thm_FuchsThesis_Daroczy_eq_2_120
-- name    : FuchsThesis.Daroczy.eq_2_120
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:20.150641+00:00
-- url     : https://prove2.me/theorems/f954be0b-fe55-48fe-807f-72bdd4984f78
-- title:
--   Eq. (2.120): $f(0)=f(1)=0$
-- statement:
--   Let $\alpha > 0$ with $\alpha \ne 1$, and let $H_\alpha : \Gamma \to \mathbb R$ be symmetric and satisfy the recursion (2.111) of type $\alpha$. Then $f(x) = H_\alpha(x, 1-x)$ vanishes at both endpoints:
--
--   $$
--   f(0) = H_\alpha(0, 1) = 0, \qquad f(1) = H_\alpha(1, 0) = 0.
--   $$
--
--   In information terms, a sure outcome carries no information. These boundary values let the closed formula for $f$ extend to $p = 0$ and $p = 1$.
--
--   Differences from the source:
--   - encoding: recursion (2.111) for every $n \ge 2$ → recursion required only when $p_1 + p_2 > 0$; reason: the right side of (2.111) is undefined at $p_1 + p_2 = 0$, so this only excludes undefined cases
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (2.116) and (2.120), pp.32–33 (PDF pp.41–42)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eqs. (2.116) and (2.120), pp.32–33 (PDF pp.41–42), in the proof of
Theorem 2.7: for a symmetric `H_α` satisfying (2.111), the function `f(x) = H_α(x, 1 − x)` of
(2.114) vanishes at both endpoints: `f(0) = 0` and `f(1) = 0`, i.e. `H_α(0, 1) = H_α(1, 0) = 0`.

**Formalization Note.** `α > 0, α ≠ 1` is the standing assumption of §2.4.1. -/
theorem eq_2_120 (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) (H : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : IsSymmetric H) (hrec : SatisfiesRecursion α H) :
    H 2 ![0, 1 - 0] = 0 ∧ H 2 ![1, 1 - 1] = 0 := by sorry

end FuchsThesis.Daroczy
