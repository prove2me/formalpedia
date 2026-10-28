-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_generator_entropy_subdifferential
-- name    : OAI.WeakHessian.RCD.generator_entropy_subdifferential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:42:18.836748+00:00
-- url     : https://prove2.me/theorems/8c5029ba-50fb-47a0-876b-af2a6a22cf52
-- title:
--   OAI.WeakHessian.RCD.generator_entropy_subdifferential: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.generator_entropy_subdifferential` of [lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/GeneratorSubgradient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/GeneratorSubgradient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianTransport`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   theorem RCD.generator_entropy_subdifferential {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
--       (o : X) {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A)
--       (hun : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m)
--       {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m, u x ≤ B)
--       (hI : Integrable (fisherDensity (m := m) u) m)
--       (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
--       (hEnt : FiniteEntropy m (μ:Measure X))
--       (T : ℝ≥0) (hT : 0 < T)
--       {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
--       (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
--       (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
--       (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
--       (hD : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
--       (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
--       {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
--       ∃ q : Measure (X×X), ∃ φ : X → ℝ,
--         IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
--         QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
--         (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
--           ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
--           (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
--             2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) ∧
--         entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*(QuadraticTransportCost q).toReal ≤
--           -(∫ x,A x*φ x ∂m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.FiniteEntropy` and `OAI.WeakHessian.entropyReal` (definitions bundle `OAIQ52Wh000` of this split); `OAI.WeakHessianTransport.densityMeasure` (definitions bundle `OAIQ52Wh001` of this split); `OAI.WeakHessian.QuadraticLipschitzBound` and `OAI.WeakHessian.fisherDensity` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.IsCoupling`, `OAI.WeakHessian.IsLaplacian`, `OAI.WeakHessian.IsOptimalCoupling`, `OAI.WeakHessian.QuadraticTransportCost` and `OAI.WeakHessian.RCD` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/GeneratorSubgradient.lean (declaration OAI.WeakHessian.RCD.generator_entropy_subdifferential)

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh000
import Definitions.Def_OAIQ52Wh001
import Definitions.Def_OAIQ52Wh002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile46
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

variable [SigmaFinite m]

theorem RCD.generator_entropy_subdifferential {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (o : X) {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m, u x ≤ B)
    (hI : Integrable (fisherDensity (m := m) u) m)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
    (hEnt : FiniteEntropy m (μ:Measure X))
    (T : ℝ≥0) (hT : 0 < T)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*(QuadraticTransportCost q).toReal ≤
        -(∫ x,A x*φ x ∂m) := by
  sorry
end WeakHessian

end
end InlinedFile46

end OAI
end
