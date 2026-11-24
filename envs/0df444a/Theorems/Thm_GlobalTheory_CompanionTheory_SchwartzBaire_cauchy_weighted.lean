-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchwartzBaire_cauchy_weighted
-- name    : GlobalTheory.CompanionTheory.SchwartzBaire.cauchy_weighted
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:11:54.29223+00:00
-- url     : https://prove2.me/theorems/1be005cb-911e-4ec8-bddb-9242b5ceff60
-- title:
--   Schwartz Baire: cauchy weighted
-- statement:
--   The Schwartz Baire construction uses the cauchy weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean#L19-L30

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

theorem GlobalTheory.CompanionTheory.SchwartzBaire.cauchy_weighted (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) (k l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ m' ≥ N, ∀ x, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖ ≤ ε := by sorry
