-- Prove2me | Theorems.Thm_GlobalTheory_EmbeddingMean_tower
-- name    : GlobalTheory.EmbeddingMean.tower
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:28.582233+00:00
-- url     : https://prove2.me/theorems/e32782ca-4f1d-4dff-afe0-904a8b05690b
-- title:
--   Embedding Mean: tower
-- statement:
--   The Embedding Mean construction uses the tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAndMean.lean#L25-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAndMean.lean#L25-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAndMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbeddingMean

theorem GlobalTheory.EmbeddingMean.tower {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] :
    (∀ f : A →ₐ[K] C, ∃ g : B →ₐ[K] C, g.comp (IsScalarTower.toAlgHom K A B) = f) ∧
    ∀ F : (A →ₐ[K] C) → ℝ,
      (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B))) / (Module.finrank K B : ℝ)
        = (∑ f : A →ₐ[K] C, F f) / (Module.finrank K A : ℝ) := by sorry
