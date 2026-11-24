-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_comm
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.word_comm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:35.131683+00:00
-- url     : https://prove2.me/theorems/f129621b-a9b0-4289-8b2b-bbdae15dca79
-- title:
--   Analytic Word: word comm
-- statement:
--   The Analytic Word construction uses the word comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L22-L26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}

theorem GlobalTheory.CompanionTheory.AnalyticWord.word_comm (Z : ι → Module.End ℂ V) (Ω : Module.End ℂ V) (hΩ : ∀ i, Ω * Z i = Z i * Ω)
    (l : List ι) : Ω * word Z l = word Z l * Ω := by sorry
