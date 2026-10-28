-- Prove2me | Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_rcd_localized_plan_law
-- name    : OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:53:20.610926+00:00
-- url     : https://prove2.me/theorems/da2225a0-d783-45c3-93af-19f8ee924c3c
-- title:
--   OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law` of [lean/OAI/Geometry/WeakHessian/WeakHessian/Transport/LocalizedPlanLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Transport/LocalizedPlanLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport`, `open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakHessianUpperBound.rcd_localized_plan_law {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
--       (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
--       {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
--       (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
--       (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
--       (u₀ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
--       (hu₀ : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u₀ x)
--       {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
--       (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
--       (hlaw₀ : densityMeasure (exponentialMeasure m (fun x => a*F x)) u₀ = π.map (fun γ => γ timeZero))
--       {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
--       {r D S : ℝ} (hD : 0 ≤ D) (x₁ : X)
--       (hs : ∀ᵐ γ ∂π,dist (γ timeOne) x₁ ≤ r)
--       (hl : ∀ᵐ γ ∂π,dist (γ timeZero) (γ timeOne) ≤ D)
--       (htracks : ∀ᵐ γ ∂π,∀ t : Time,dist (γ t) o < S)
--       {d β R T U c δ : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
--       (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 m)
--       (hlocal : ∀ x,dist x o < R → G x ≤ c)
--       (hT : 0 ≤ T) (hTU : T < U) (hδ : 0 < δ)
--       (hsmall : 4*a*(CG+|c|)*U*localizedHeatM K a CG U ≤ 1) :
--       ∃ μ : ProbabilityMeasure X, FiniteEntropy m (μ:Measure X) ∧
--         (μ:Measure X) ≤ (B : ℝ≥0∞) • m ∧
--         (∀ᵐ x ∂(μ:Measure X),dist x x₁ ≤ r+δ*D) ∧
--         ∀ (f : X →ᵇ ℝ),HasCompactSupport (f : X → ℝ) → ∀ q : ℝ,0 < q →
--         (∫ x,boundedHopfMap f (q+1) x ∂(μ:Measure X))-
--           (∫ x,boundedHopfMap f q x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)) ≤
--         planKineticCost π/2*localizedActionBound K a c CG T+
--           curvatureTailBound K a c CG U (hopfUniformLip f q)
--             (((B:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF)) d β R S+
--           T*(entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
--             entropyReal (exponentialMeasure m (fun x => a*F x))
--               (densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.FiniteEntropy` and `OAI.WeakHessian.entropyReal` (definitions bundle `OAIQ52Wh000` of this split); `OAI.WeakHessianTransport.densityMeasure` (definitions bundle `OAIQ52Wh001` of this split); `OAI.WeakHessian.curvatureTailBound`, `OAI.WeakHessian.exponentialMeasure`, `OAI.WeakHessian.hopfUniformLip`, `OAI.WeakHessian.localizedActionBound` and `OAI.WeakHessian.localizedHeatM` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessianTransport.boundedHopfMap` (definitions bundle `OAIQ52Wh003` of this split); `OAI.WeakHessian.planKineticCost` (definitions bundle `OAIQ52Wh004` of this split); `OAI.WeakHessian.cheegerHeat` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.BoundedTracks`, `OAI.WeakHessian.Curve`, `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.IsGeodesic`, `OAI.WeakHessian.IsTestPlan`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.Time`, `OAI.WeakHessian.WeakHessianUpperBound`, `OAI.WeakHessian.curveMeasurableSpace`, `OAI.WeakHessian.timeOne` and `OAI.WeakHessian.timeZero` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.every_geodesic` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Transport/LocalizedPlanLaw.lean (declaration OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law)

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_localized_plan_law {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (u₀ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    (hu₀ : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u₀ x)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
    (hlaw₀ : densityMeasure (exponentialMeasure m (fun x => a*F x)) u₀ = π.map (fun γ => γ timeZero))
    {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {r D S : ℝ} (hD : 0 ≤ D) (x₁ : X)
    (hs : ∀ᵐ γ ∂π,dist (γ timeOne) x₁ ≤ r)
    (hl : ∀ᵐ γ ∂π,dist (γ timeZero) (γ timeOne) ≤ D)
    (htracks : ∀ᵐ γ ∂π,∀ t : Time,dist (γ t) o < S)
    {d β R T U c δ : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 m)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    (hT : 0 ≤ T) (hTU : T < U) (hδ : 0 < δ)
    (hsmall : 4*a*(CG+|c|)*U*localizedHeatM K a CG U ≤ 1) :
    ∃ μ : ProbabilityMeasure X, FiniteEntropy m (μ:Measure X) ∧
      (μ:Measure X) ≤ (B : ℝ≥0∞) • m ∧
      (∀ᵐ x ∂(μ:Measure X),dist x x₁ ≤ r+δ*D) ∧
      ∀ (f : X →ᵇ ℝ),HasCompactSupport (f : X → ℝ) → ∀ q : ℝ,0 < q →
      (∫ x,boundedHopfMap f (q+1) x ∂(μ:Measure X))-
        (∫ x,boundedHopfMap f q x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)) ≤
      planKineticCost π/2*localizedActionBound K a c CG T+
        curvatureTailBound K a c CG U (hopfUniformLip f q)
          (((B:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF)) d β R S+
        T*(entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
          entropyReal (exponentialMeasure m (fun x => a*F x))
            (densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀))) := by
  sorry
end WeakHessian

end
end

end OAI
end
