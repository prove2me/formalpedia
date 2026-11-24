-- Prove2me | Theorems.Thm_GlobalTheory_T_tail_sum_over_places_small
-- name    : GlobalTheory.T.tail_sum_over_places_small
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:59:49.836465+00:00
-- url     : https://prove2.me/theorems/f8cbbc77-2c3c-4615-82bd-e2856a8654e4
-- title:
--   T: tail sum over places small
-- statement:
--   The T construction uses the tail sum over places small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TailSumOverPlacesSmallStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TailSumOverPlacesSmallStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmall
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmallStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tail_sum_over_places_small : ∀ (F : Type) [Field F] [NumberField F] (C : ℝ), 0 ≤ C → ∀ η : ℝ, 0 < η → ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, T₀ ⊆ T → ∀ U : Finset (HeightOneSpectrum (𝓞 F)), ∑ D ∈ U.powerset with ¬ D ⊆ T, ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ≤ η := by sorry
