-- Prove2me | Theorems.Thm_GlobalTheory_Phase_WeilPV_pv_mul
-- name    : GlobalTheory.Phase.WeilPV.pv_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:45.9765+00:00
-- url     : https://prove2.me/theorems/7ae7de5a-1d15-4b01-ad20-9be0579e0a26
-- title:
--   Weil PV: pv mul
-- statement:
--   The Weil PV construction uses the pv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RootOfUnityPhaseVacuumSiegelThetaTransform.lean#L108-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RootOfUnityPhaseVacuumSiegelThetaTransform.lean#L108-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplectic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeisenbergOperatorRationalPointLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralGaussianShapeRootOfUnityPhStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSIntertwines
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RootOfUnityPhaseVacuumSiegelThetaTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.WeilPV
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.Phase.WeilPV.pv_mul (he : Even (Fintype.card κ)) {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (H : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ)
    (H' : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ' φ ψ → PV φ → PV ψ) :
    ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (σ' * σ) φ ψ → PV φ → PV ψ := by sorry
