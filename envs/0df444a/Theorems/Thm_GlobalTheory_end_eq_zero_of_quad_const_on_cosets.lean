-- Prove2me | Theorems.Thm_GlobalTheory_end_eq_zero_of_quad_const_on_cosets
-- name    : GlobalTheory.end_eq_zero_of_quad_const_on_cosets
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:10.818095+00:00
-- url     : https://prove2.me/theorems/6e34120d-c427-4679-a7f2-d54847181555
-- title:
--   Global Theory: end eq zero of quad const on cosets
-- statement:
--   The Global Theory construction uses the end eq zero of quad const on cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L45-L55

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem GlobalTheory.end_eq_zero_of_quad_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (ω : LinearMap.BilinForm R M) (hω : Injective ω) (S : M →ₗ[R] M)
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : Rˣ) (q : M → R)
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, q t = c) : S = 0 := by sorry
