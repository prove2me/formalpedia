-- Prove2me | Theorems.Thm_OAI_WeakHessian_cheegerHeat_plan_entropy_dual_error
-- name    : OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:54:31.14201+00:00
-- url     : https://prove2.me/theorems/8c350319-cfc6-472a-872d-88c3ecf82ef1
-- title:
--   OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error` of [lean/OAI/Geometry/WeakHessian/WeakHessian/Transport/PerturbedPlanDual.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Transport/PerturbedPlanDual.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional`, `open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction`):
--
--   ```lean
--   lemma cheegerHeat_plan_entropy_dual_error
--       (hfin : FiniteOnBoundedSets m) (o : X)
--       (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
--         ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
--       (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
--       {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
--       (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
--       {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
--       {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
--       (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
--       (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
--       (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
--       {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
--       (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1)
--       {δ T q : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hq : 0 < q)
--       (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ))
--       {b : ℝ → ℝ} (hbc : ContinuousOn b (Ici 0)) (hbp : ∀ t,0 ≤ t → 0 < b t)
--       {R : ℝ → Lp ℝ 2 m → ℝ} {Eerror : ℝ}
--       (hgrad : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m, Sobolev m (v : X → ℝ) →
--         b (backwardsHeatTime δ T s)*(∫ x,smoothDensity κ u s x*
--           (weakGradient m (cheegerHeat h (backwardsHeatTime δ T s) v) x)^2 ∂m) ≤
--           (∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient m v x)^2 ∂m)+R s v)
--       (hsplit : ∀ s ∈ Ico (0:ℝ) 1, ∀ v w : Lp ℝ 2 m,Sobolev m (v : X → ℝ) → Sobolev m (w : X → ℝ) →
--         ∀ t : ℝ,R s (v+t•w) ≤ 2*R s v+2*t^2*R s w)
--       (hrelative : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m,Sobolev m (v : X → ℝ) →
--         2*R s v ≤ ∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient m v x)^2 ∂m)
--       (herror : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m,Sobolev m (v : X → ℝ) →
--         (∀ᵐ x ∂m,|weakGradient m v x| ≤ hopfUniformLip f q) → R s v ≤ Eerror) :
--       ∀ ε, 0 < ε →
--         (∫ x, cheegerHeat h δ (smoothDensity κ u 1) x*boundedHopfMap f (q+1) x ∂m)-
--           (∫ x, cheegerHeat h (δ+T) (smoothDensity κ u 0) x*boundedHopfMap f q x ∂m)+
--         T*((∫ x, regularizedEntropy ε (cheegerHeat h (δ+T) (smoothDensity κ u 0) x) ∂m)-
--           (∫ x, regularizedEntropy ε (cheegerHeat h δ (smoothDensity κ u 1) x) ∂m)) ≤
--         (∫ s in (0:ℝ)..1, planKineticCost π/b (backwardsHeatTime δ T s)/2)+Eerror+
--           ε*compactHopfDualBound hfin o f hf hq/2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessianTransport.densityMeasure` (definitions bundle `OAIQ52Wh001` of this split); `OAI.WeakHessian.LocalGradientParallelogram`, `OAI.WeakHessian.backwardsHeatTime`, `OAI.WeakHessian.hopfUniformLip` and `OAI.WeakHessian.regularizedEntropy` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessianTransport.boundedHopfMap` (definitions bundle `OAIQ52Wh003` of this split); `OAI.WeakHessian.planKineticCost` and `OAI.WeakHessian.smoothDensity` (definitions bundle `OAIQ52Wh004` of this split); `OAI.WeakHessian.cheegerHeat` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.compactHopfDualBound` (definitions bundle `OAIQ52Wh007` of this split); `OAI.WeakHessian.BoundedTracks`, `OAI.WeakHessian.Curve`, `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.IsGeodesic`, `OAI.WeakHessian.IsTestPlan`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.Sobolev`, `OAI.WeakHessian.Time`, `OAI.WeakHessian.cheegerEnergy`, `OAI.WeakHessian.curveMeasurableSpace` and `OAI.WeakHessian.weakGradient` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Transport/PerturbedPlanDual.lean (declaration OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error)

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007

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
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma cheegerHeat_plan_entropy_dual_error
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1)
    {δ T q : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hq : 0 < q)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ))
    {b : ℝ → ℝ} (hbc : ContinuousOn b (Ici 0)) (hbp : ∀ t,0 ≤ t → 0 < b t)
    {R : ℝ → Lp ℝ 2 m → ℝ} {Eerror : ℝ}
    (hgrad : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m, Sobolev m (v : X → ℝ) →
      b (backwardsHeatTime δ T s)*(∫ x,smoothDensity κ u s x*
        (weakGradient m (cheegerHeat h (backwardsHeatTime δ T s) v) x)^2 ∂m) ≤
        (∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient m v x)^2 ∂m)+R s v)
    (hsplit : ∀ s ∈ Ico (0:ℝ) 1, ∀ v w : Lp ℝ 2 m,Sobolev m (v : X → ℝ) → Sobolev m (w : X → ℝ) →
      ∀ t : ℝ,R s (v+t•w) ≤ 2*R s v+2*t^2*R s w)
    (hrelative : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m,Sobolev m (v : X → ℝ) →
      2*R s v ≤ ∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient m v x)^2 ∂m)
    (herror : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m,Sobolev m (v : X → ℝ) →
      (∀ᵐ x ∂m,|weakGradient m v x| ≤ hopfUniformLip f q) → R s v ≤ Eerror) :
    ∀ ε, 0 < ε →
      (∫ x, cheegerHeat h δ (smoothDensity κ u 1) x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, cheegerHeat h (δ+T) (smoothDensity κ u 0) x*boundedHopfMap f q x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h (δ+T) (smoothDensity κ u 0) x) ∂m)-
        (∫ x, regularizedEntropy ε (cheegerHeat h δ (smoothDensity κ u 1) x) ∂m)) ≤
      (∫ s in (0:ℝ)..1, planKineticCost π/b (backwardsHeatTime δ T s)/2)+Eerror+
        ε*compactHopfDualBound hfin o f hf hq/2 := by
  sorry

end WeakHessian

end
end

end OAI
end
