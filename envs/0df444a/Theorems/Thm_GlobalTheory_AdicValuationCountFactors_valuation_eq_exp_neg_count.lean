-- Prove2me | Theorems.Thm_GlobalTheory_AdicValuationCountFactors_valuation_eq_exp_neg_count
-- name    : GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:26.763897+00:00
-- url     : https://prove2.me/theorems/941e6cea-df49-4b6f-8731-b35c97c54e33
-- title:
--   Adic Valuation Count Factors: valuation eq exp neg count
-- statement:
--   The Adic Valuation Count Factors construction uses the valuation eq exp neg count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationAlgebraMapEqCount.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationAlgebraMapEqCount.lean#L20-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.AdicValuationCountFactors
variable {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (spanSingleton R⁰ x)) := by sorry
