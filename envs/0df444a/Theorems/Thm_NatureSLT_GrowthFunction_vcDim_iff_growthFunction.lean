-- Prove2me | Theorems.Thm_NatureSLT_GrowthFunction_vcDim_iff_growthFunction
-- name    : NatureSLT.GrowthFunction.vcDim_iff_growthFunction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:40.192159+00:00
-- url     : https://prove2.me/theorems/b40d2320-47d5-4ff4-9f37-3b964cfdcd09
-- title:
--   Section 3.6 — the VC dimension by shattering agrees with the VC dimension by the growth function
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of indicator functions on a nonempty set $Z$, with $\Lambda$ nonempty, and let $G^\Lambda(\ell) = \ln \sup_{z_1, \dots, z_\ell} N^\Lambda(z_1, \dots, z_\ell)$ be its growth function. The VC dimension of the set, defined as the maximum number of vectors it shatters, is the same as the VC dimension defined through the growth function:
--
--   1. the VC dimension is infinite if and only if the growth function is linear,
--   $$G^\Lambda(\ell) = \ell \ln 2 \quad \text{for every } \ell \ge 0;$$
--   2. for every integer $h \ge 0$, the VC dimension equals $h$ if and only if
--   $$G^\Lambda(h) = h \ln 2 \quad \text{and} \quad G^\Lambda(h + 1) < (h + 1) \ln 2 .$$
--
--   This is the sense in which the book calls the shattering definition an *equivalent* definition of the VC dimension: the integer $h$ of Theorem 3.3 is the largest number of points the set of functions can shatter.
--
--   **Formalization Note** Indicator values are booleans (`true` = $1$), and the VC dimension takes values in $\mathbb N \cup \{\infty\}$. Nonemptiness of $Z$ and $\Lambda$ is assumed so that the supremum in the growth function is over a nonempty set of samples and is at least $1$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 80, Section 3.6 (equivalent definition of the VC dimension of a set of indicator functions)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_growthFunction
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

namespace NatureSLT.GrowthFunction

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.6, p. 80: the definition of
the VC dimension by shattering is **equivalent** to the definition through the growth function
(p. 79). The VC dimension is infinite exactly when `G^Λ(ℓ) = ℓ ln 2` for every `ℓ`, and it equals
the integer `h` exactly when `G^Λ(h) = h ln 2` and `G^Λ(h + 1) < (h + 1) ln 2` (the `h` of
Theorem 3.3). -/
theorem vcDim_iff_growthFunction {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool) :
    (vcDim Q = ⊤ ↔ ∀ ℓ : ℕ, growthFunction Q ℓ = (ℓ : ℝ) * Real.log 2) ∧
    ∀ h : ℕ, (vcDim Q = (h : ℕ∞) ↔
      (growthFunction Q h = (h : ℝ) * Real.log 2 ∧
        growthFunction Q (h + 1) < ((h + 1 : ℕ) : ℝ) * Real.log 2)) := by sorry

end NatureSLT.GrowthFunction
