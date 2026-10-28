-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_cheegerHeat_comparison_integrated
-- name    : OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:48:53.216569+00:00
-- url     : https://prove2.me/theorems/50eae555-d72e-4e18-9392-00170b0bc748
-- title:
--   OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated` of [lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/IntegratedEVI.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/IntegratedEVI.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianTransport`, `open scoped Topology ENNReal NNReal`):
--
--   ```lean
--   lemma RCD.cheegerHeat_comparison_integrated {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
--       (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
--       (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
--       (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
--       {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
--       {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
--       (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
--       (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
--       (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
--       (hw : Integrable (fun x => Real.exp (-V x)) m)
--       (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
--       (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
--       (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
--       {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
--       (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
--       (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
--       {b : ℝ} (hb : 0 ≤ b) :
--       (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
--         quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
--         ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.entropyReal` (definitions bundle `OAIQ52Wh000` of this split); `OAI.WeakHessianTransport.densityMeasure` (definitions bundle `OAIQ52Wh001` of this split); `OAI.WeakHessian.quadraticWassersteinSq` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.IsFormGenerator` (definitions bundle `OAIQ52Wh004` of this split); `OAI.WeakHessian.cheegerHeat` and `OAI.WeakHessian.cheeger_closedQuadraticEnergy` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.RCD` and `OAI.WeakHessian.cheegerEnergy` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.RCD.cheegerHeat_comparison_weighted` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/IntegratedEVI.lean (declaration OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated)

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

section InlinedFile52
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_comparison_integrated {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    {b : ℝ} (hb : 0 ≤ b) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
      quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)) := by
  sorry
end WeakHessian

end
end InlinedFile52

end OAI
end
