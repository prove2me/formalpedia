-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_pderiv_map
-- name    : GlobalTheory.FormalCalc.pderiv_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:48.725281+00:00
-- url     : https://prove2.me/theorems/e463ac89-5582-40fe-89da-91601d51c7f1
-- title:
--   Formal Calc: pderiv map
-- statement:
--   The Formal Calc construction uses the pderiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L104-L107

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

theorem GlobalTheory.FormalCalc.pderiv_map {T : Type*} [CommRing T] (φ : R →+* T) (i : σ) (f : MvPowerSeries σ R) :
    pderiv T i (map φ f) = map φ (pderiv R i f) := by sorry
