-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_IterPattern_mem_reindex_J
-- name    : GlobalTheory.SymChain.IterPattern.mem_reindex_J
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:09.123852+00:00
-- url     : https://prove2.me/theorems/d816d9bb-5027-41c7-8c7a-98a69b9f09a6
-- title:
--   Iter Pattern: mem reindex J
-- statement:
--   The Iter Pattern construction uses the mem reindex J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainPatternIterated.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainPatternIterated.lean#L24-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.IterPattern
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SymChain.IterPattern.mem_reindex_J {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J := by sorry
