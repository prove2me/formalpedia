-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_UpperLaw_elem_mul_fill
-- name    : GlobalTheory.PartRed.UpperLaw.elem_mul_fill
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:28.881429+00:00
-- url     : https://prove2.me/theorems/1586a489-fd29-440e-b880-e01d7e07c8dd
-- title:
--   Upper Law: elem mul fill
-- statement:
--   The Upper Law construction uses the elem mul fill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean#L94-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean#L94-L154

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

theorem GlobalTheory.PartRed.UpperLaw.elem_mul_fill (l m : Fin c) (i : Fin (c + 1)) (h : l ≠ m) (hmi : m.val = i.val) (hl : l.val < i.val)
    (hi : i.val ≤ ρ) (h1 : transSet ρ ⊆ I) (h2 : (upSet ρ).filter (fun e => i.val < colIx e) ⊆ I)
    (hI : I ⊆ transSet ρ ∪ upSet ρ) (hli : (Sum.inr l, Sum.inr i) ∉ I) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) :
    (embA n (elem l m h a)).val * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y
      = fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I (x + Matrix.single (Sum.inr l) (Sum.inr i) a)
          (y + shear ρ I l m a x y) := by sorry
