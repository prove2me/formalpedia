-- Prove2me | Theorems.Thm_NatureSLT_GrowthFunction_growth_bound_of_vcDim
-- name    : NatureSLT.GrowthFunction.growth_bound_of_vcDim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:36.940844+00:00
-- url     : https://prove2.me/theorems/fbb33bd5-cb71-48cf-b466-3d87b18c0171
-- title:
--   Eq. (3.23) — finite VC dimension h gives G(ℓ) ≤ h(ln(ℓ/h) + 1) for ℓ > h
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of indicator functions on a nonempty set $Z$, with $\Lambda$ nonempty, that possesses a finite VC dimension $h$ (the maximum number of vectors it shatters). Then its growth function satisfies
--
--   $$G^\Lambda(\ell) \le h\left(\ln \frac{\ell}{h} + 1\right) \qquad \text{for every integer } \ell > h. \tag{3.23}$$
--
--   The bound turns the growth function, a supremum over all samples, into an explicit function of $\ell$ and $h$; it is what makes the distribution-free bounds of Chapter 3 constructive (Eq. (3.24) substitutes it into the bounds on the risk).
--
--   **Formalization Note** At $h = 0$ the expression $h(\ln(\ell/h) + 1)$ is undefined in the book; the formal statement evaluates it as $0$ (division by zero and $\ln 0$ are both $0$ in Lean), which is also the limit of $h(\ln(\ell/h) + 1)$ as $h \to 0^+$. In that case all functions coincide on every point, $N^\Lambda \equiv 1$ and $G^\Lambda \equiv 0$, so the value $0$ is the bound intended. Indicator values are booleans (`true` = $1$).
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 83, Eq. (3.23)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_growthFunction
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

namespace NatureSLT.GrowthFunction

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.7, p. 83, Eq. (3.23): for a
set of indicator functions with finite VC dimension `h`,
`G^Λ(ℓ) ≤ h (ln (ℓ / h) + 1)` for every `ℓ > h`. At `h = 0` the right-hand side is `0`
(`0 · (ln(ℓ/0) + 1)` with Lean's `ℓ / 0 = 0`, `ln 0 = 0`), which is also the limit of
`h (ln(ℓ/h) + 1)` as `h → 0⁺`. -/
theorem growth_bound_of_vcDim {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool)
    (h : ℕ) (hvc : vcDim Q = (h : ℕ∞)) :
    ∀ ℓ : ℕ, h < ℓ →
      growthFunction Q ℓ ≤ (h : ℝ) * (Real.log ((ℓ : ℝ) / (h : ℝ)) + 1) := by sorry

end NatureSLT.GrowthFunction
