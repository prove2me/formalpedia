-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_pderiv_powerSeries_subst
-- name    : GlobalTheory.FormalCalc.pderiv_powerSeries_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:48.845146+00:00
-- url     : https://prove2.me/theorems/0e468960-84b9-4554-88d8-a0c1c9438035
-- title:
--   Formal Calc: pderiv power Series subst
-- statement:
--   The Formal Calc construction uses the pderiv power Series subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L88-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem GlobalTheory.FormalCalc.pderiv_powerSeries_subst {a : MvPowerSeries τ S} (ha : PowerSeries.HasSubst a)
    (f : PowerSeries R) (j : τ) :
    pderiv S j (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative R f) * pderiv S j a := by sorry
