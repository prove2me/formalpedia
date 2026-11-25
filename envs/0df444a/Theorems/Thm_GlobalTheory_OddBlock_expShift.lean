-- Prove2me | Theorems.Thm_GlobalTheory_OddBlock_expShift
-- name    : GlobalTheory.OddBlock.expShift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:34:57.297464+00:00
-- url     : https://prove2.me/theorems/ec1ce107-f5a6-4820-b405-a82471f06424
-- title:
--   Odd Block: exp Shift
-- statement:
--   The Odd Block construction uses the exp Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean#L319-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean#L319-L323

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
import Theorems.Thm_GlobalTheory_BlockValue_Lead_prod
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_exp
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000

theorem GlobalTheory.OddBlock.expShift : (∀ (C : Type) [Field C] [CharZero C] (κ κ' : Type) [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] (ζ : κ' → MvPolynomial κ C) (F : MvPolynomial κ C) (G : MvPolynomial κ' C) (g : MvPowerSeries (κ ⊕ κ') C),
    (∑ A ∈ ((MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G : MvPolynomial (κ ⊕ κ') C)).support, MvPolynomial.coeff A ((MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G : MvPolynomial (κ ⊕ κ') C)) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (PowerSeries.subst (((∑ j, MvPolynomial.rename Sum.inl (ζ j) * MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C) : MvPowerSeries (κ ⊕ κ') C)) (PowerSeries.exp C) * g)) =
    ∑ m ∈ (MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl (ζ j) + MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C)) G).support, MvPolynomial.coeff m (MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl (ζ j) + MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C)) G) * ((Finsupp.sumFinsuppEquivProdFinsupp m).2.prod fun _ e => (e.factorial : C)) *
      (∑ A ∈ (F).support, MvPolynomial.coeff A (F) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) * (show MvPowerSeries κ C from fun A' => MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (A', (Finsupp.sumFinsuppEquivProdFinsupp m).2)) g)))) := by sorry
