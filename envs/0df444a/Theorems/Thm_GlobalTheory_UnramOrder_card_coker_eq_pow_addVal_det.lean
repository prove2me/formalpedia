-- Prove2me | Theorems.Thm_GlobalTheory_UnramOrder_card_coker_eq_pow_addVal_det
-- name    : GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:26.058208+00:00
-- url     : https://prove2.me/theorems/9eae055e-a65b-49d8-ad93-9876dfbf3ffd
-- title:
--   Unram Order: card coker eq pow add Val det
-- statement:
--   The Unram Order construction uses the card coker eq pow add Val det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardCokernelUnramifiedOrderMatrixOfDetBase.lean#L40-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardCokernelUnramifiedOrderMatrixOfDetBase.lean#L40-L115

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (f : M →ₗ[R] M) (hf : LinearMap.det f ≠ 0) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R (LinearMap.det f)).toNat := by sorry
