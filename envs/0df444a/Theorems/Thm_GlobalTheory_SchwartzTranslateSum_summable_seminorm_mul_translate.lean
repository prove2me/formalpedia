-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzTranslateSum_summable_seminorm_mul_translate
-- name    : GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:49.657588+00:00
-- url     : https://prove2.me/theorems/f5c71b93-3012-4f87-8fd4-46c9294d553e
-- title:
--   Schwartz Translate Sum: summable seminorm mul translate
-- statement:
--   The Schwartz Translate Sum construction uses the summable seminorm mul translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeTranslatesCutoffSummable.lean#L23-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeTranslatesCutoffSummable.lean#L23-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeTranslatesCutoffSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchwartzMap
noncomputable section
open GlobalTheory GlobalTheory.SchwartzTranslateSum

theorem GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h f : SchwartzMap V ℂ) (hh : HasCompactSupport h)
    (u : Λ → SchwartzMap V ℂ) (hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x) (k n : ℕ) :
    Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by sorry
