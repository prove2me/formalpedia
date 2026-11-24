-- Prove2me | Theorems.Thm_GlobalTheory_SW_FourierJ_ft_eq
-- name    : GlobalTheory.SW.FourierJ.ft_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:16.67178+00:00
-- url     : https://prove2.me/theorems/2b0088ab-5ac7-4950-a4e4-9623886f0f8c
-- title:
--   Fourier J: ft eq
-- statement:
--   The Fourier J construction uses the ft eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitarySiegelThetaTransformationLawStandar.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitarySiegelThetaTransformationLawStandar.lean#L157-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.FourierJ.ft_eq [DecidableEq κ] [DecidableEq ι] {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι ℚ → ℂ}
    (h : HasLevel R φ) {y : Matrix κ ι ℚ} (hy : IntM ((R : ℚ) • y)) :
    ft φ y = ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ *
      ∑ n : κ → ι → Fin (R * R), φ (rep R n) * ech (pr (rep R n) y) := by sorry
