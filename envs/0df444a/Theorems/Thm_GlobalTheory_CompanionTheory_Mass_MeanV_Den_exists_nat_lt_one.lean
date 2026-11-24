-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Den_exists_nat_lt_one
-- name    : GlobalTheory.CompanionTheory.Mass.MeanV.Den.exists_nat_lt_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:52:29.744622+00:00
-- url     : https://prove2.me/theorems/c4553f58-c14f-47e7-8b5f-4a959d42a4e4
-- title:
--   Den: exists nat lt one
-- statement:
--   The Den construction uses the exists nat lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIntegralMultipleBoundedPlaces.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIntegralMultipleBoundedPlaces.lean#L48-L54

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV GlobalTheory.CompanionTheory.Mass.MeanV.Den
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.Mass.MeanV.Den.exists_nat_lt_one (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ v.valuation F (p : F) < 1 := by sorry
