-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_continuous_pderiv
-- name    : GlobalTheory.FormalCalc.continuous_pderiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:34:01.824376+00:00
-- url     : https://prove2.me/theorems/bc07a43c-d4f8-4d9d-9481-5886cb62d668
-- title:
--   Formal Calc: continuous pderiv
-- statement:
--   The Formal Calc construction uses the continuous pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L35-L41

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
open MvPowerSeries.WithPiTopology

theorem GlobalTheory.FormalCalc.continuous_pderiv [TopologicalSpace R] [DiscreteTopology R] (i : σ) :
    Continuous (pderiv R i : MvPowerSeries σ R → MvPowerSeries σ R) := by sorry
