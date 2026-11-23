-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst
-- name    : GlobalTheory.FormalCalc.pderiv_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:21.450606+00:00
-- url     : https://prove2.me/theorems/9c1667d0-5a94-45eb-86cf-07c7824c5dda
-- title:
--   Formal Calc: pderiv subst
-- statement:
--   The Formal Calc construction uses the pderiv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L56-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L56-L86

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

theorem GlobalTheory.FormalCalc.pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (j : τ) :
    pderiv S j (subst a f) = ∑ i, subst a (pderiv R i f) * pderiv S j (a i) := by sorry
