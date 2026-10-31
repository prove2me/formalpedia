-- Prove2me | Theorems.Thm_FuchsThesis_Daroczy_eq_2_119
-- name    : FuchsThesis.Daroczy.eq_2_119
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:31.134653+00:00
-- url     : https://prove2.me/theorems/58ed96a3-7ae5-42b4-8c16-028f5170cc17
-- title:
--   Eq. (2.119): the functional equation of information of type $\alpha$
-- statement:
--   Let $\alpha > 0$ with $\alpha \ne 1$, and let $H_\alpha : \Gamma \to \mathbb R$ be symmetric and satisfy the recursion (2.111) of type $\alpha$. Then $f(x) = H_\alpha(x, 1-x)$ satisfies the functional equation
--
--   $$
--   f(x) + (1-x)^{\alpha} f\!\left(\frac{y}{1-x}\right) = f(y) + (1-y)^{\alpha} f\!\left(\frac{x}{1-y}\right)
--   $$
--
--   for all $x, y \in [0, 1)$ with $x + y \le 1$.
--
--   For $\alpha = 1$ this is the fundamental equation of information. It is obtained by computing $H_\alpha(x, y, 1-x-y) = H_\alpha(y, x, 1-x-y)$ in two ways with the recursion, and it is the only property of $H_\alpha$ used to determine $f$.
--
--   Differences from the source:
--   - encoding: recursion (2.111) for every $n \ge 2$ → recursion required only when $p_1 + p_2 > 0$; reason: the right side of (2.111) is undefined at $p_1 + p_2 = 0$, so this only excludes undefined cases
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.119), p.33 (PDF p.42)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.119), p.33 (PDF p.42), in the proof of Theorem 2.7: for a
symmetric `H_α` satisfying (2.111), the function `f(x) = H_α(x, 1 − x)` of (2.114) satisfies the
functional equation
`f(x) + (1 − x)^α f(y/(1 − x)) = f(y) + (1 − y)^α f(x/(1 − y))`
for `x, y ∈ [0, 1)` with `x + y ≤ 1`.

**Formalization Note.** `f(t)` is written out as `H 2 ![t, 1 - t]`; on the stated domain all
arguments of `f` lie in `[0, 1]` and no denominator vanishes. `α > 0, α ≠ 1` is the standing
assumption of §2.4.1. -/
theorem eq_2_119 (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) (H : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : IsSymmetric H) (hrec : SatisfiesRecursion α H)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1) (hxy : x + y ≤ 1) :
    H 2 ![x, 1 - x] + (1 - x) ^ α * H 2 ![y / (1 - x), 1 - y / (1 - x)]
      = H 2 ![y, 1 - y] + (1 - y) ^ α * H 2 ![x / (1 - y), 1 - x / (1 - y)] := by sorry

end FuchsThesis.Daroczy
