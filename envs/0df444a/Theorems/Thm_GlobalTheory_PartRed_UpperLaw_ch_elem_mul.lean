-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_UpperLaw_ch_elem_mul
-- name    : GlobalTheory.PartRed.UpperLaw.ch_elem_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:31.41206+00:00
-- url     : https://prove2.me/theorems/23f53146-5d6c-45b7-b04e-1feacd787261
-- title:
--   Upper Law: ch elem mul
-- statement:
--   The Upper Law construction uses the ch elem mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean#L156-L158

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

theorem GlobalTheory.PartRed.UpperLaw.ch_elem_mul (l m : Fin c) (h : l ≠ m) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((embA n (elem l m h a)).val * t) = ch t + a * t (Sum.inr m) (Sum.inr l.succ) := by sorry
