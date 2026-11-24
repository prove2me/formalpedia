-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_LowLaw_rowAdd_mul_apply
-- name    : GlobalTheory.PartRed.LowLaw.rowAdd_mul_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:53:09.524128+00:00
-- url     : https://prove2.me/theorems/3988672a-7ea4-4a06-bc35-f20f04e3c236
-- title:
--   Low Law: row Add mul apply
-- statement:
--   The Low Law construction uses the row Add mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionLowerEntryMultiplicationLaw.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionLowerEntryMultiplicationLaw.lean#L15-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.LowLaw
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n'] [DecidableEq n']

theorem GlobalTheory.PartRed.LowLaw.rowAdd_mul_apply (r l : Fin c) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (p : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) :
    ((fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) p q =
      t p q + if p = Sum.inr r then a * t (Sum.inr l) q else 0 := by sorry
