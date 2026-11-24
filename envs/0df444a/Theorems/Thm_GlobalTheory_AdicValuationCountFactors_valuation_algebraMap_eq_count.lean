-- Prove2me | Theorems.Thm_GlobalTheory_AdicValuationCountFactors_valuation_algebraMap_eq_count
-- name    : GlobalTheory.AdicValuationCountFactors.valuation_algebraMap_eq_count
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:54:32.983116+00:00
-- url     : https://prove2.me/theorems/a2ead07e-5637-436f-9ceb-8bb0ea14c991
-- title:
--   Adic Valuation Count Factors: valuation algebra Map eq count
-- statement:
--   The Adic Valuation Count Factors construction uses the valuation algebra Map eq count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationAlgebraMapEqCount.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationAlgebraMapEqCount.lean#L11-L18

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

theorem GlobalTheory.AdicValuationCountFactors.valuation_algebraMap_eq_count {r : R} (hr : r ≠ 0) :
    v.valuation K (algebraMap R K r) =
      WithZero.exp (-FractionalIdeal.count K v (spanSingleton R⁰ (algebraMap R K r))) := by sorry
