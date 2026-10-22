-- Prove2me | Theorems.Thm_NatureSLT_GrowthFunction_growth_function_dichotomy
-- name    : NatureSLT.GrowthFunction.growth_function_dichotomy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:41.84039+00:00
-- url     : https://prove2.me/theorems/9a6e66c4-f906-41ec-9f62-c32b9e61d09b
-- title:
--   Theorem 3.3 — the growth function is linear or bounded by h(ln(ℓ/h) + 1)
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of indicator functions on a nonempty set $Z$, with $\Lambda$ nonempty, and let
--
--   $$G^\Lambda(\ell) = \ln \sup_{z_1, \dots, z_\ell} N^\Lambda(z_1, \dots, z_\ell)$$
--
--   be its growth function, where $N^\Lambda(z_1, \dots, z_\ell)$ is the number of different binary vectors $(Q(z_1, \alpha), \dots, Q(z_\ell, \alpha))$, $\alpha \in \Lambda$. Then at least one of the following holds (the two cannot hold together, since the second has $G^\Lambda(h+1) < (h+1)\ln 2$):
--
--   1. the growth function is linear: $G^\Lambda(\ell) = \ell \ln 2$ for every $\ell \ge 0$; or
--   2. there is an integer $h \ge 0$ with
--   $$G^\Lambda(h) = h \ln 2, \qquad G^\Lambda(h + 1) < (h + 1) \ln 2,$$
--   and for this $h$
--   $$G^\Lambda(\ell) \le h\left(\ln \frac{\ell}{h} + 1\right) \qquad \text{for every integer } \ell > h .$$
--
--   In other words, the growth function is either linear or bounded by a logarithmic function; it cannot, for example, behave like $c\sqrt{\ell}$. The integer $h$ is the VC dimension of the set of functions; it is determined by the two conditions on $G^\Lambda(h)$ and $G^\Lambda(h+1)$ (a fact the formal statement does not need to assert, since it only requires such an $h$ to exist).
--
--   **Formalization Note** The theorem's display carries no range for the logarithmic bound; the range $\ell > h$ is the one the book gives in both of its restatements, the display after the Definition on p. 79 ("$(\ell > h)$") and Eq. (3.23) on p. 83 ("In this case Theorem 3.3 states that the bound (3.23) holds", with "$\ell > h$"). Read for every $\ell$ the bound is false (finding F1 of this mission). At $h = 0$ the expression $h(\ln(\ell/h) + 1)$ is evaluated as $0$ (division by zero and $\ln 0$ are $0$ in Lean), the limit as $h \to 0^+$; in that case $G^\Lambda \equiv 0$. Indicator values are booleans (`true` = $1$); $Z$ and $\Lambda$ are assumed nonempty so that the supremum is over a nonempty set of samples and is at least $1$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 79, Theorem 3.3 (range ℓ > h from the display on p. 79 and Eq. (3.23), p. 83)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_growthFunction

namespace NatureSLT.GrowthFunction

/-- **Theorem 3.3** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.5, p. 79).
Any growth function either satisfies `G^Λ(ℓ) = ℓ ln 2` (for every `ℓ`), or there is an integer
`h` with `G^Λ(h) = h ln 2` and `G^Λ(h + 1) < (h + 1) ln 2` such that
`G^Λ(ℓ) ≤ h (ln (ℓ / h) + 1)`. The bound is stated for `ℓ > h`, the range the book gives in both
of its restatements (the display after the Definition on p. 79 and (3.23) on p. 83). The `h`
is unique. At `h = 0` the right-hand side is `0` (Lean's `ℓ / 0 = 0`, `ln 0 = 0`), the limit of
`h (ln(ℓ/h) + 1)` as `h → 0⁺`. -/
theorem growth_function_dichotomy {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool) :
    (∀ ℓ : ℕ, growthFunction Q ℓ = (ℓ : ℝ) * Real.log 2) ∨
    (∃ h : ℕ, growthFunction Q h = (h : ℝ) * Real.log 2 ∧
      growthFunction Q (h + 1) < ((h + 1 : ℕ) : ℝ) * Real.log 2 ∧
      ∀ ℓ : ℕ, h < ℓ →
        growthFunction Q ℓ ≤ (h : ℝ) * (Real.log ((ℓ : ℝ) / (h : ℝ)) + 1)) := by sorry

end NatureSLT.GrowthFunction
