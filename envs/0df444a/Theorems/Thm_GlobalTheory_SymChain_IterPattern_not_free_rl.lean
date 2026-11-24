-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_IterPattern_not_free_rl
-- name    : GlobalTheory.SymChain.IterPattern.not_free_rl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:00.182551+00:00
-- url     : https://prove2.me/theorems/0ee90752-5f86-406c-8fd0-f4a4454e81c4
-- title:
--   Iter Pattern: not free rl
-- statement:
--   The Iter Pattern construction uses the not free rl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainPatternIterated.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainPatternIterated.lean#L37-L41

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
variable {ρ κ l j : ℕ} {t : Type}

theorem GlobalTheory.SymChain.IterPattern.not_free_rl (s : t) (y : Ix (Fin κ ⊕ Fin l) t j) :
    ¬ FreeIx ρ (ixSucc _ t j (.inr s)) (ixSucc _ t j (.inl y)) := by sorry
