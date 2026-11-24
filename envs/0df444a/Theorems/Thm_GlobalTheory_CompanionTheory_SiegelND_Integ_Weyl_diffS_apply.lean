-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_diffS_apply
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.diffS_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:46.409539+00:00
-- url     : https://prove2.me/theorems/e57194d2-72bd-41e7-9831-1af1e209f288
-- title:
--   Weyl: diff S apply
-- statement:
--   The Weyl construction uses the diff S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L98-L99

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.diffS_apply (f : SchwartzMap V ℂ) (y x : V) :
    diffS f y x = f (x + y) * conj (f x) := by sorry
