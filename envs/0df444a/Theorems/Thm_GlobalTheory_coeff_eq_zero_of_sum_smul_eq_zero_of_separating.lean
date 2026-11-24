-- Prove2me | Theorems.Thm_GlobalTheory_coeff_eq_zero_of_sum_smul_eq_zero_of_separating
-- name    : GlobalTheory.coeff_eq_zero_of_sum_smul_eq_zero_of_separating
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:11.307856+00:00
-- url     : https://prove2.me/theorems/59ec14fc-53c3-4e80-bd78-0d3121fa278b
-- title:
--   Global Theory: coeff eq zero of sum smul eq zero of separating
-- statement:
--   The Global Theory construction uses the coeff eq zero of sum smul eq zero of separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffEqZeroOfSumSmulEqZeroOfSeparating.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffEqZeroOfSumSmulEqZeroOfSeparating.lean#L9-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffEqZeroOfSumSmulEqZeroOfSeparating
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.coeff_eq_zero_of_sum_smul_eq_zero_of_separating {Y A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (P : (Y → A) → Prop) (h1 : P 1)
    (hmul : ∀ t t', P t → P t' → P (t * t')) (s : Finset Y)
    (hsep : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → ∃ t, P t ∧ IsUnit (t y - t z))
    (a : Y → M) (h : ∀ t, P t → ∑ y ∈ s, t y • a y = 0) : ∀ y ∈ s, a y = 0 := by sorry
