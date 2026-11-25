-- Prove2me | Theorems.Thm_GlobalTheory_OddBlock_ExpShift_pair_eq_mixed
-- name    : GlobalTheory.OddBlock.ExpShift.pair_eq_mixed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:47.345661+00:00
-- url     : https://prove2.me/theorems/61a54e5c-601f-40ef-937b-26be76c7e169
-- title:
--   Exp Shift: pair eq mixed
-- statement:
--   The Exp Shift construction uses the pair eq mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean#L237-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean#L237-L258

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NewtonBoundPosAndNewtonStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SumEqOfIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.ExpShift
variable {C : Type} [Field C] {κ κ' : Type}

theorem GlobalTheory.OddBlock.ExpShift.pair_eq_mixed (ζ : κ' → MvPolynomial κ C) (F : MvPolynomial κ C)
    (E : MvPowerSeries (κ ⊕ κ') C) (h0 : ∀ g, slice 0 (E * g) = slice 0 g)
    (hd : ∀ j, MvPowerSeries.pderiv C (Sum.inr j) E =
      E * ((MvPolynomial.rename Sum.inl (ζ j) : MvPolynomial (κ ⊕ κ') C) : MvPowerSeries (κ ⊕ κ') C))
    (G : MvPolynomial κ' C) : ∀ g : MvPowerSeries (κ ⊕ κ') C,
    pair (MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G) (E * g) =
      mixed F (MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl (ζ j) +
        MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C)) G) g := by sorry
