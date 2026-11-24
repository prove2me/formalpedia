-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_eq_one_of_mem_slice_of_mul_mem_slice
-- name    : GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:15:10.629227+00:00
-- url     : https://prove2.me/theorems/58d03ffc-7274-4f8e-9177-f7e6fc1bd336
-- title:
--   Rank Fibre Ker: eq one of mem slice of mul mem slice
-- statement:
--   The Rank Fibre Ker construction uses the eq one of mem slice of mul mem slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SliceStabilizerTrivial.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SliceStabilizerTrivial.lean#L7-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivial
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

theorem GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k) :
    Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1 := by sorry
