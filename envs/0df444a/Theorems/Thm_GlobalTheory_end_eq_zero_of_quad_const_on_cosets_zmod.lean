-- Prove2me | Theorems.Thm_GlobalTheory_end_eq_zero_of_quad_const_on_cosets_zmod
-- name    : GlobalTheory.end_eq_zero_of_quad_const_on_cosets_zmod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:46.244904+00:00
-- url     : https://prove2.me/theorems/9d963388-1e5f-49d8-8177-282bc57faef9
-- title:
--   Global Theory: end eq zero of quad const on cosets zmod
-- statement:
--   The Global Theory construction uses the end eq zero of quad const on cosets zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L90-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L90-L101

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

theorem GlobalTheory.end_eq_zero_of_quad_const_on_cosets_zmod {ι : Type*} (hn : Odd n)
    (ω : LinearMap.BilinForm (ZMod (n ^ k)) (ι → ZMod (n ^ k))) (hω : Injective ω)
    (S : (ι → ZMod (n ^ k)) →ₗ[ZMod (n ^ k)] (ι → ZMod (n ^ k)))
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : (ZMod (n ^ k))ˣ) (q : (ι → ZMod (n ^ k)) → ZMod (n ^ k))
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set (ι → ZMod (n ^ k)))
    (hT : (∀ x, ∃ t ∈ T, ∃ a, x = t + n • a) ∨ (2 ≤ k ∧ ∀ x, ∃ t ∈ T, n • (x - t) = 0))
    (c : ZMod (n ^ k)) (hc : ∀ t ∈ T, q t = c) : S = 0 := by sorry
