-- Prove2me | Theorems.Thm_GlobalTheory_DiscreteSeriesTest_rhoN_add_rhoC
-- name    : GlobalTheory.DiscreteSeriesTest.rhoN_add_rhoC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:51.434804+00:00
-- url     : https://prove2.me/theorems/2f2b58a8-4c55-4a33-8150-42e3d344ef7a
-- title:
--   Discrete Series Test: rho N add rho C
-- statement:
--   The Discrete Series Test construction uses the rho N add rho C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L11-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.DiscreteSeriesTest

theorem GlobalTheory.DiscreteSeriesTest.rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    rhoN ε a + rhoC ε a = ((n : ℝ) - 1) / 2 - a := by sorry
