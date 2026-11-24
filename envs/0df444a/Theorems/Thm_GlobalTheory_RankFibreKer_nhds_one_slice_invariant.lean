-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_nhds_one_slice_invariant
-- name    : GlobalTheory.RankFibreKer.nhds_one_slice_invariant
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:20.327344+00:00
-- url     : https://prove2.me/theorems/fd5f6a74-30ed-4ca9-9963-50c125d9cd58
-- title:
--   Rank Fibre Ker: nhds one slice invariant
-- statement:
--   The Rank Fibre Ker construction uses the nhds one slice invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSliceSectionIntegral.lean#L7-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSliceSectionIntegral.lean#L7-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer

theorem GlobalTheory.RankFibreKer.nhds_one_slice_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB k a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice k a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by sorry
