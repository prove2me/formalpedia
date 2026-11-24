-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tsum_unitVec_eq
-- name    : GlobalTheory.CompanionTheory.Mass.MeanV.tsum_unitVec_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:19:33.281845+00:00
-- url     : https://prove2.me/theorems/aef76a80-d51f-47de-920d-359e0060d399
-- title:
--   Mean V: tsum unit Vec eq
-- statement:
--   The Mean V construction uses the tsum unit Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TruncatedSumLimit.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TruncatedSumLimit.lean#L10-L21

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV

theorem GlobalTheory.CompanionTheory.Mass.MeanV.tsum_unitVec_eq {F : Type} [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (h : F → ℝ) :
    ∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}, h (x.1 ()) =
      ∑' x : F, (IntOut T).indicator h x := by sorry
