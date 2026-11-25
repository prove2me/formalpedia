-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_PureColPf_affPt_col
-- name    : GlobalTheory.LocFlat.PureColPf.affPt_col
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:43.038986+00:00
-- url     : https://prove2.me/theorems/e423e0eb-2cde-4210-a311-09d74be6f393
-- title:
--   Pure Col Pf: aff Pt col
-- statement:
--   The Pure Col Pf construction uses the aff Pt col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L34-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
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
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] {n n' ι ι' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

theorem GlobalTheory.LocFlat.PureColPf.affPt_col (p : ℕ) (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : n) (q : Fin (c + 1)) (hq : q.val + 1 = p) : affPt p x₀ e (.inl a) (.inr q) = 0 := by sorry
