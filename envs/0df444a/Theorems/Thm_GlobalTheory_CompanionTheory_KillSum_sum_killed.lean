-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KillSum_sum_killed
-- name    : GlobalTheory.CompanionTheory.KillSum.sum_killed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:50:50.281167+00:00
-- url     : https://prove2.me/theorems/5871195b-f807-4276-b1f0-abba1f6b2372
-- title:
--   Kill Sum: sum killed
-- statement:
--   The Kill Sum construction uses the sum killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorSumAnnihilator.lean#L38-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorSumAnnihilator.lean#L38-L53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorSumAnnihilator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KillSum

theorem GlobalTheory.CompanionTheory.KillSum.sum_killed {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ) :
    ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by sorry
