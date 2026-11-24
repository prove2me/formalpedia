-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NumberFieldCoord_abs_repr_le_of_forall_norm_embedding_le
-- name    : GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:01.134179+00:00
-- url     : https://prove2.me/theorems/0dec636d-91a3-48d6-8292-04e2cd0f77cf
-- title:
--   Number Field Coord: abs repr le of forall norm embedding le
-- statement:
--   The Number Field Coord construction uses the abs repr le of forall norm embedding le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegerCoordinatesBound.lean#L6-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegerCoordinatesBound.lean#L6-L45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegerCoordinatesBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NumberFieldCoord

theorem GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le :
    ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)),
      Function.Surjective (fun i => InfinitePlace.mk (τ i)) →
      ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) →
        ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by sorry
