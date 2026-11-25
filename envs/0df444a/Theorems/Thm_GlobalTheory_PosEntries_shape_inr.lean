-- Prove2me | Theorems.Thm_GlobalTheory_PosEntries_shape_inr
-- name    : GlobalTheory.PosEntries.shape_inr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:11:37.200075+00:00
-- url     : https://prove2.me/theorems/486e1da2-3e81-47fc-b6c2-cb318b337d9f
-- title:
--   Pos Entries: shape inr
-- statement:
--   The Pos Entries construction uses the shape inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeBlockDiagonalTargetEntryConditions.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeBlockDiagonalTargetEntryConditions.lean#L12-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.PosEntries
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.PosEntries.shape_inr {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i : Fin c) (s : n ⊕ Fin c)
    (hs : M (Sum.inr i) s ≠ 0) : s = Sum.inr i := by sorry
