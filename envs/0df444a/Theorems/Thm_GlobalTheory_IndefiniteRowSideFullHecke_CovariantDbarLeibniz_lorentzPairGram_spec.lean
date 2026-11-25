-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantDbarLeibniz_lorentzPairGram_spec
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.lorentzPairGram_spec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:25.299786+00:00
-- url     : https://prove2.me/theorems/fa70d44e-17e5-4c72-b1eb-730fd5471d8e
-- title:
--   Covariant Dbar Leibniz: lorentz Pair Gram spec
-- statement:
--   The Covariant Dbar Leibniz construction uses the lorentz Pair Gram spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean#L192-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean#L192-L218

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.lorentzPairGram_spec : IsHermFrame (Metric.ball 0 1) lorentzPairGram ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, IsUnit (subField lorentzPairGram z).det) ∧
    ¬ (lorentzPairGram 0).PosDef := by sorry
