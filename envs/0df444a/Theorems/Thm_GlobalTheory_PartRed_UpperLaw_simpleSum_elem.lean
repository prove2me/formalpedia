-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_UpperLaw_simpleSum_elem
-- name    : GlobalTheory.PartRed.UpperLaw.simpleSum_elem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:04.637666+00:00
-- url     : https://prove2.me/theorems/8a34ee55-88b9-4742-8a77-c9223282a7cf
-- title:
--   Upper Law: simple Sum elem
-- statement:
--   The Upper Law construction uses the simple Sum elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean#L41-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLaw
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
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.PartRed.UpperLaw.simpleSum_elem (l m : Fin c) (h : l ≠ m) (a : k) :
    simpleSum (embA n (elem l m h a)) = if m.val = l.val + 1 then a else 0 := by sorry
