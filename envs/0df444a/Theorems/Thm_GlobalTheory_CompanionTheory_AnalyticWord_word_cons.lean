-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_cons
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.word_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:37.91299+00:00
-- url     : https://prove2.me/theorems/4d5d472b-a3ba-4514-9fae-cf7c338dfb56
-- title:
--   Analytic Word: word cons
-- statement:
--   The Analytic Word construction uses the word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L16-L17

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

theorem GlobalTheory.CompanionTheory.AnalyticWord.word_cons (Z : ι → Module.End ℂ V) (i : ι) (l : List ι) :
    word Z (i :: l) = Z i * word Z l := by sorry
