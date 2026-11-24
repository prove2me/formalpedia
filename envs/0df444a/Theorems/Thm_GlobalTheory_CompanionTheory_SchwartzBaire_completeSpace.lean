-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchwartzBaire_completeSpace
-- name    : GlobalTheory.CompanionTheory.SchwartzBaire.completeSpace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:11:55.541797+00:00
-- url     : https://prove2.me/theorems/1fbf7f0d-4592-406c-b384-d1629f8a5590
-- title:
--   Schwartz Baire: complete Space
-- statement:
--   The Schwartz Baire construction uses the complete Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean#L104-L106

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchwartzBaire
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem GlobalTheory.CompanionTheory.SchwartzBaire.completeSpace [CompleteSpace F] : CompleteSpace 𝓢(E, F) := by sorry
