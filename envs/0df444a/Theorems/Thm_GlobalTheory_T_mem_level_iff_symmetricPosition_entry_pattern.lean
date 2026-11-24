-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_level_iff_symmetricPosition_entry_pattern
-- name    : GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:21.706441+00:00
-- url     : https://prove2.me/theorems/b25aa830-5d5b-44d7-a45f-1c7d22aa0149
-- title:
--   T: mem level iff symmetric Position entry pattern
-- statement:
--   The T construction uses the mem level iff symmetric Position entry pattern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffSymmetricPositionEntryPatternStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffSymmetricPositionEntryPatternStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (g : GL (Fin κ ⊕ Fin (s + 1)) k), g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by sorry
