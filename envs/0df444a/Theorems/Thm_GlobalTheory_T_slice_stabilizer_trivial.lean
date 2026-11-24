-- Prove2me | Theorems.Thm_GlobalTheory_T_slice_stabilizer_trivial
-- name    : GlobalTheory.T.slice_stabilizer_trivial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:57:48.56583+00:00
-- url     : https://prove2.me/theorems/3d4827b7-525c-40f4-b0c6-c8e58060e1c6
-- title:
--   T: slice stabilizer trivial
-- statement:
--   The T construction uses the slice stabilizer trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SliceStabilizerTrivialStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SliceStabilizerTrivialStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivialStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.slice_stabilizer_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1 := by sorry
