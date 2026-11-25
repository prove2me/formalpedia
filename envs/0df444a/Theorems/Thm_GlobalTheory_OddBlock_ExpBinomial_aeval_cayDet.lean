-- Prove2me | Theorems.Thm_GlobalTheory_OddBlock_ExpBinomial_aeval_cayDet
-- name    : GlobalTheory.OddBlock.ExpBinomial.aeval_cayDet
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:33:49.550143+00:00
-- url     : https://prove2.me/theorems/7c4a845a-cdbb-5fa1-89bf-8eac94f560e4
-- title:
--   Exp Binomial: aeval cay Det
-- statement:
--   The Exp Binomial construction uses the aeval cay Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean#L470-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean#L470-L497

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
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.ExpBinomial

theorem GlobalTheory.OddBlock.ExpBinomial.aeval_cayDet (C : Type) [Field C] (l L E n : ℕ) (hl : (l : C) ≠ 0) :
    MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl
      (MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X j ^ L : MvPolynomial (Fin n × Fin n) C) +
        MvPolynomial.X (Sum.inr j) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C))
      (cayDet n C) =
    MvPolynomial.C ((-((l : C) ^ E)⁻¹) ^ n) *
      (MvPolynomial.map (Int.castRingHom C) (psi l L E n) +
        MvPolynomial.rename Sum.inl (cayDet n C ^ L)) := by sorry
