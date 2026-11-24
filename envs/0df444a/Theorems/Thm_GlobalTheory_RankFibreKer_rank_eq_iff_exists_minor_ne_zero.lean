-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_rank_eq_iff_exists_minor_ne_zero
-- name    : GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:44.096026+00:00
-- url     : https://prove2.me/theorems/c7645b18-52aa-4ea9-afac-f9ab0167ffd9
-- title:
--   Rank Fibre Ker: rank eq iff exists minor ne zero
-- statement:
--   The Rank Fibre Ker construction uses the rank eq iff exists minor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FullRankIffNonzeroMinor.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FullRankIffNonzeroMinor.lean#L7-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankIffNonzeroMinor
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

theorem GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) :
    Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by sorry
