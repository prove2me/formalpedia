-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_LowLaw_simpleSum_elem
-- name    : GlobalTheory.PartRed.LowLaw.simpleSum_elem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:52:33.623332+00:00
-- url     : https://prove2.me/theorems/9a301e8a-fd07-49ab-9622-eacc480211b1
-- title:
--   Low Law: simple Sum elem
-- statement:
--   The Low Law construction uses the simple Sum elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionLowerEntryMultiplicationLaw.lean#L122-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionLowerEntryMultiplicationLaw.lean#L122-L147

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

theorem GlobalTheory.PartRed.LowLaw.simpleSum_elem (r l : Fin c) (h : r ≠ l) (a : k) :
    simpleSum (embA n (elem r l h a)) = if l.val = r.val + 1 then a else 0 := by sorry
