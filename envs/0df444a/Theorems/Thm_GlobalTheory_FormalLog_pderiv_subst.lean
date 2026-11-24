-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_pderiv_subst
-- name    : GlobalTheory.FormalLog.pderiv_subst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:03:47.687277+00:00
-- url     : https://prove2.me/theorems/eb965170-4320-43bf-b09f-15cc10cb32ab
-- title:
--   Formal Log: pderiv subst
-- statement:
--   The Formal Log construction uses the pderiv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqCOfPderivZero.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqCOfPderivZero.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {σ τ : Type}

theorem GlobalTheory.FormalLog.pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv k t (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k t (a s) := by sorry
