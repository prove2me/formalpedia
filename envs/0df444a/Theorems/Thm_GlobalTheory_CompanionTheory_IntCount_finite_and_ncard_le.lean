-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IntCount_finite_and_ncard_le
-- name    : GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:48:36.017861+00:00
-- url     : https://prove2.me/theorems/0c46f5bd-2e44-4d9e-adfe-9416b383ce6c
-- title:
--   Int Count: finite and ncard le
-- statement:
--   The Int Count construction uses the finite and ncard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegersBoundedArchimedeanCount.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegersBoundedArchimedeanCount.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FiniteAndNcardBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegersBoundedArchimedeanCount
import Theorems.Thm_UpperTheory_Reformulated_B_FiniteAndNcardBound_finite_and_ncard_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding Module
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IntCount

theorem GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
      {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
      ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N := by sorry
