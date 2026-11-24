-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_LowLaw_embA_elem_val
-- name    : GlobalTheory.PartRed.LowLaw.embA_elem_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:53:09.972869+00:00
-- url     : https://prove2.me/theorems/09c59ed7-cde3-4ff3-ba46-f0a6679f9637
-- title:
--   Low Law: emb A elem val
-- statement:
--   The Low Law construction uses the emb A elem val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionLowerEntryMultiplicationLaw.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionLowerEntryMultiplicationLaw.lean#L99-L100

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

theorem GlobalTheory.PartRed.LowLaw.embA_elem_val (r l : Fin c) (h : r ≠ l) (a : k) :
    (embA n (elem r l h a)).val = fromBlocks 1 0 0 (transvection r l a) := by sorry
