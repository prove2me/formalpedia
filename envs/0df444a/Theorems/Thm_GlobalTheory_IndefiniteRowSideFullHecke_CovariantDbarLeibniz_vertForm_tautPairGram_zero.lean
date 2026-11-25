-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantDbarLeibniz_vertForm_tautPairGram_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.vertForm_tautPairGram_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:23.703038+00:00
-- url     : https://prove2.me/theorems/e98d5a16-17f7-4e0f-b5f9-89a3ac7e1652
-- title:
--   Covariant Dbar Leibniz: vert Form taut Pair Gram zero
-- statement:
--   The Covariant Dbar Leibniz construction uses the vert Form taut Pair Gram zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean#L171-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean#L171-L187

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.vertForm_tautPairGram_zero (ξ η : ℂ) :
    vertForm tautPairGram 0 ξ η = kappa * (ξ * conj η) := by sorry
