-- Prove2me | Theorems.Thm_GlobalTheory_T_full_rank_iff_nonzero_minor
-- name    : GlobalTheory.T.full_rank_iff_nonzero_minor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:33.982571+00:00
-- url     : https://prove2.me/theorems/337a1852-7289-4772-8c4d-a3224262c19d
-- title:
--   T: full rank iff nonzero minor
-- statement:
--   The T construction uses the full rank iff nonzero minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FullRankIffNonzeroMinorStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FullRankIffNonzeroMinorStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankIffNonzeroMinor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankIffNonzeroMinorStatement
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

theorem GlobalTheory.T.full_rank_iff_nonzero_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by sorry
