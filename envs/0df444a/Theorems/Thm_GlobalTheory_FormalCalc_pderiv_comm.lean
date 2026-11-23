-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_pderiv_comm
-- name    : GlobalTheory.FormalCalc.pderiv_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:21.231059+00:00
-- url     : https://prove2.me/theorems/26d57801-c2a7-46be-9024-6c7675ee2471
-- title:
--   Formal Calc: pderiv comm
-- statement:
--   The Formal Calc construction uses the pderiv comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L43-L52

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

theorem GlobalTheory.FormalCalc.pderiv_comm (i j : σ) (f : MvPowerSeries σ R) :
    pderiv R i (pderiv R j f) = pderiv R j (pderiv R i f) := by sorry
