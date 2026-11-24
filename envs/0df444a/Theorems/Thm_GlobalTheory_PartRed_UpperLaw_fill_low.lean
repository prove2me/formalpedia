-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_UpperLaw_fill_low
-- name    : GlobalTheory.PartRed.UpperLaw.fill_low
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:25.921267+00:00
-- url     : https://prove2.me/theorems/f5381e83-ec95-4db1-88d7-35580d3a312e
-- title:
--   Upper Law: fill low
-- statement:
--   The Upper Law construction uses the fill low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean#L74-L87

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
variable {ρ : ℕ} {I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))}

theorem GlobalTheory.PartRed.UpperLaw.fill_low (hI : I ⊆ transSet ρ ∪ upSet ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k)
    (m : Fin c) (j : Fin (c + 1)) (hj : j.val ≤ m.val) (hm : j.val ≤ ρ) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y (Sum.inr m) (Sum.inr j)
      = if m.val = j.val then 1 else 0 := by sorry
