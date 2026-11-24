-- Prove2me | Theorems.Thm_GlobalTheory_SW_FourierJ_tsum_supp
-- name    : GlobalTheory.SW.FourierJ.tsum_supp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:39:23.717745+00:00
-- url     : https://prove2.me/theorems/4ed01b89-41eb-4dcb-9297-0a5cf1e03adb
-- title:
--   Fourier J: tsum supp
-- statement:
--   The Fourier J construction uses the tsum supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitarySiegelThetaTransformationLawStandar.lean#L259-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitarySiegelThetaTransformationLawStandar.lean#L259-L271

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

theorem GlobalTheory.SW.FourierJ.tsum_supp {R : ℕ} (hR : 0 < R) {ψ : Matrix κ ι ℚ → ℂ} (h : HasLevel R ψ)
    (G : Matrix κ ι ℚ → ℂ) :
    ∑' y, ψ y * G y = ∑' m : κ → ι → ℤ, ψ ((R : ℚ)⁻¹ • zm m) * G ((R : ℚ)⁻¹ • zm m) := by sorry
