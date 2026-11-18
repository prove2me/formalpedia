-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_2
-- name    : Kyprianou.Ch09.stageC_result_9_2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T15:23:08.814992+00:00
-- url     : https://prove2.me/theorems/6f4a9c03-067e-4520-accf-7d9b8b75e652
-- title:
--   Result 9.2: McKean put value and optimal threshold
-- statement:
--   Result 9.2. Model and parameter assumptions: Strike K>0; q>0, OR q=0 AND lim_(t→∞)X_t=+∞ almost surely. T is the set of all ℱ-stopping times; exponential horizon e_q independent when q>0 and e_0=∞ by convention. Running infimum underline X_t=inf_(0≤s≤t)X_s. Quantifiers and stopping-time domain: Every x∈ℝ, expectation under the initial-X=x shift; no q=0 negative-drift case. Mathematical assertion: Let m=E[exp(underline X_(e_q))] and x*=log(Km). Then τ*=inf{t>0:X_t<x*} is optimal for v(x)=sup_T E_x[e^(−qT)(K−e^(X_T))⁺], and v(x)=E[(K m−exp(x+underline X_(e_q)))⁺]/m. Endpoint and source qualification: Same as printed. For q=0 and X_t→+∞, underline X_∞ is finite a.s.; show m∈(0,1] and time-0/first strict downcrossing admissibility, rather than assuming X_t→−∞. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.2; original PDF pp. [250]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceMcKean
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_2 :
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q K : ℝ)
    (hX : B1.SourceModel P X F)
    (hK : 0 < K) (hDomain : B1.McKeanDomain P ν X q e),
    let m := B1.killedInfimumMoment P ν X e
    0 < m ∧ m ≤ 1 ∧
    ∀ x : ℝ,
      let z := Real.log (K * m)
      let τ := fun ω => B1.firstStrictBelow
        (fun t ξ => x + X t ξ) z ω
      B1.AdmissibleStop F τ ∧
      B1.optionValue P F X (B1.putGain K) q x (fun _ => 0) =
        B1.mckeanPutFormula P ν X e K x ∧
      B1.optionValue P F X (B1.putGain K) q x (fun _ => 0) =
        (∫ ω, B1.stoppedGain X (B1.putGain K) q x
          (fun _ => 0) τ ω ∂P) := by
  sorry

end Kyprianou.Ch09
