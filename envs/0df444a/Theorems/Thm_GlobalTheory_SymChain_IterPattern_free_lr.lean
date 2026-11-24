-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_IterPattern_free_lr
-- name    : GlobalTheory.SymChain.IterPattern.free_lr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:11.738331+00:00
-- url     : https://prove2.me/theorems/4e248f87-569b-4d82-8d41-1a66da4a3303
-- title:
--   Iter Pattern: free lr
-- statement:
--   The Iter Pattern construction uses the free lr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainPatternIterated.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainPatternIterated.lean#L33-L35

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

theorem GlobalTheory.SymChain.IterPattern.free_lr (x : Ix (Fin κ ⊕ Fin l) t j) (s : t) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inr s)) := by sorry
