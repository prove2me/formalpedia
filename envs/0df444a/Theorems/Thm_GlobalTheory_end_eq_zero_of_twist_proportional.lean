-- Prove2me | Theorems.Thm_GlobalTheory_end_eq_zero_of_twist_proportional
-- name    : GlobalTheory.end_eq_zero_of_twist_proportional
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:45.543999+00:00
-- url     : https://prove2.me/theorems/20058343-2f02-4d17-908f-bbcf787877a3
-- title:
--   Global Theory: end eq zero of twist proportional
-- statement:
--   The Global Theory construction uses the end eq zero of twist proportional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L103-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L103-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory
variable {n k : ℕ}

theorem GlobalTheory.end_eq_zero_of_twist_proportional {ι K : Type*} [CommRing K] [IsDomain K] (hn : Odd n)
    (ω : LinearMap.BilinForm (ZMod (n ^ k)) (ι → ZMod (n ^ k))) (hω : Injective ω)
    (S : (ι → ZMod (n ^ k)) →ₗ[ZMod (n ^ k)] (ι → ZMod (n ^ k)))
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : (ZMod (n ^ k))ˣ) (q : (ι → ZMod (n ^ k)) → ZMod (n ^ k))
    (hq : ∀ x, 2 * q x = u * ω (S x) x) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ k))
    (θ θ' : (ι → ZMod (n ^ k)) → K) (hθ : ∀ x, θ' x = ζ ^ (q x).val * θ x)
    (c : K) (hc : ∀ x, θ' x = c * θ x)
    (hT : (∀ x, ∃ t, θ t ≠ 0 ∧ ∃ a, x = t + n • a) ∨
      (2 ≤ k ∧ ∀ x, ∃ t, θ t ≠ 0 ∧ n • (x - t) = 0)) : S = 0 := by sorry
