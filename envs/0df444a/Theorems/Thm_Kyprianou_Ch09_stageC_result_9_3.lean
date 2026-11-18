-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_3
-- name    : Kyprianou.Ch09.stageC_result_9_3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T15:23:51.727187+00:00
-- url     : https://prove2.me/theorems/954af7ce-cee9-4e46-b786-be61c6055491
-- title:
--   Result 9.3: Spectrally negative McKean scale-function formula
-- statement:
--   Result 9.3. Model and parameter assumptions: Theorem 9.2 assumptions, X spectrally negative, q≥0 in permitted regime, p=q−ψ(1) may be negative; Esscher scale functions must be defined at signed p and Φ_1(p)=Φ(q)−1. Quantifiers and stopping-time domain: Every x∈ℝ and valid K>0, q; treat q−ψ(1)=0 by a justified limit rather than direct quotient. Mathematical assertion: v(x)=K Z^(q)(x−x*)−e^x Z_1^(p)(x−x*); x*=log(K·q(Φ(q)−1)/(Φ(q)(q−ψ(1)))). Corrected or extended source case: Printed scale expression with a continuous limiting threshold when q=ψ(1)>0, Φ(q)=1 and ψ′(1)>0: e^(x*)=K q/ψ′(1). Other simultaneous q=0 or Φ(q)=0 cases require independent limit/domain proof. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.3; original PDF pp. [252]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceMcKean
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_3 :
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q K : ℝ) (ψ : ℝ → ℝ) (W : ℝ → ℝ)
    (φ : ℝ)
    (hX : B1.SourceModel P X F)
    (hK : 0 < K) (hDomain : B1.McKeanDomain P ν X q e)
    (hSN : B1.HasNoPositiveJumps P X)
    (hψ : B1.HasLaplaceExponent P X ψ)
    (hφ : 0 ≤ φ ∧ ψ φ = q ∧
      ∀ θ : ℝ, 0 ≤ θ → ψ θ = q → θ ≤ φ)
    (hW : B1.IsScale ψ q W),
    let W1 := fun y : ℝ => Real.exp (-y) * W y
    let m := B1.killedInfimumMoment P ν X e
    let z := Real.log (K * m)
    (0 < m ∧
      ∀ x : ℝ,
        B1.optionValue P F X (B1.putGain K) q x (fun _ => 0) =
        K * B1.scaleZ q W (x - z) -
        Real.exp x * B1.scaleZ (q - ψ 1) W1 (x - z)) ∧
    (φ ≠ 0 → q ≠ ψ 1 →
       z = Real.log (K * (q * (φ - 1)) / (φ * (q - ψ 1)))) ∧
    (q = ψ 1 → 0 < q → 0 < deriv ψ 1 →
       Real.exp z = K * q / deriv ψ 1) := by
  sorry

end Kyprianou.Ch09
