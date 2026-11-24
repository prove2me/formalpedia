-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchwartzBaire_baireSpace
-- name    : GlobalTheory.CompanionTheory.SchwartzBaire.baireSpace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:12:06.809804+00:00
-- url     : https://prove2.me/theorems/92fac971-9bed-4628-998f-39b9aa69d2b4
-- title:
--   Schwartz Baire: baire Space
-- statement:
--   The Schwartz Baire construction uses the baire Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean#L108-L111

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

theorem GlobalTheory.CompanionTheory.SchwartzBaire.baireSpace [CompleteSpace F] : BaireSpace 𝓢(E, F) := by sorry
