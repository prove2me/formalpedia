-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_NonZeroAt_typeFrame_bas_val
-- name    : GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:50.674464+00:00
-- url     : https://prove2.me/theorems/a4006389-a409-5243-9ac9-984e84d71370
-- title:
--   Non Zero At: type Frame bas val
-- statement:
--   The Non Zero At construction uses the type Frame bas val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/StandardOrderSymmInr.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/StandardOrderSymmInr.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_StandardOrderSymmInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.NonZeroAt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by sorry
