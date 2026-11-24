-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantDbarLeibniz_contDiff_tautPairGram
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.contDiff_tautPairGram
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:12.530801+00:00
-- url     : https://prove2.me/theorems/27153bb8-a5ff-497b-8d28-3c08b1745d97
-- title:
--   Covariant Dbar Leibniz: cont Diff taut Pair Gram
-- statement:
--   The Covariant Dbar Leibniz construction uses the cont Diff taut Pair Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean#L152-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean#L152-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l k : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.contDiff_tautPairGram (a b : Unit ⊕ Unit) :
    ContDiff ℝ ∞ fun x => tautPairGram x a b := by sorry
