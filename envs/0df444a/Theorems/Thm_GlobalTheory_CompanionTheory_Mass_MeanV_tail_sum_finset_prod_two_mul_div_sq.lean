-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tail_sum_finset_prod_two_mul_div_sq
-- name    : GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:59.650213+00:00
-- url     : https://prove2.me/theorems/b1c1c761-6470-4ca8-9b0b-fc398ed080a7
-- title:
--   Mean V: tail sum finset prod two mul div sq
-- statement:
--   The Mean V construction uses the tail sum finset prod two mul div sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TailSumOverPlacesSmall.lean#L10-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TailSumOverPlacesSmall.lean#L10-L64

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SummableOneDivAbsNormSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmall
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV

theorem GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq :
    ∀ (F : Type) [Field F] [NumberField F] (C : ℝ), 0 ≤ C → ∀ η : ℝ, 0 < η →
      ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, T₀ ⊆ T →
        ∀ U : Finset (HeightOneSpectrum (𝓞 F)),
          ∑ D ∈ U.powerset with ¬ D ⊆ T,
            ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ≤ η := by sorry
