-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_cheegerHeat_contraction_weighted
-- name    : OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:50:53.479799+00:00
-- url     : https://prove2.me/theorems/e324bc72-c255-434c-89aa-262f26adcf47
-- title:
--   OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted` of [lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/HeatContraction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/HeatContraction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianTransport`, `open scoped Topology ENNReal NNReal`):
--
--   ```lean
--   lemma RCD.cheegerHeat_contraction_weighted {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
--       (h : QuadraticCheegerEnergy m) (u v : Lp ℝ 2 m)
--       (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
--       (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
--       {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
--       (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
--       {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
--       (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
--       (hU' : MemLp (fun x => v x*Real.exp (V x)) 2 m)
--       (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
--       (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
--       (hdecayi : Integrable (fun x => Real.exp (-V x)) m)
--       (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
--       (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
--       (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m ∧
--         MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
--       (μ ν : ℝ → ProbabilityMeasure X)
--       (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
--       (hν : ∀ t,0 ≤ t → (ν t:Measure X) = densityMeasure m (cheegerHeat h t v))
--       {b : ℝ} (hb : 0 ≤ b) :
--       Real.exp (2*K*b)*quadraticWassersteinSq (μ b:Measure X) (ν b:Measure X) ≤
--         quadraticWassersteinSq (μ 0:Measure X) (ν 0:Measure X)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessianTransport.densityMeasure` (definitions bundle `OAIQ52Wh001` of this split); `OAI.WeakHessian.quadraticWassersteinSq` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessian.cheegerHeat` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.QuadraticCheegerEnergy` and `OAI.WeakHessian.RCD` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proofs of `OAI.WeakHessian.RCD.cheegerHeat_reversePoincare_pointwise`, `OAI.WeakHessian.RCD.test_gradientSquare_sobolev`, `OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated` and `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality` of this split import it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/HeatContraction.lean (declaration OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted)

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

section InlinedFile73
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_contraction_weighted {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hU' : MemLp (fun x => v x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hdecayi : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m ∧
      MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (μ ν : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (hν : ∀ t,0 ≤ t → (ν t:Measure X) = densityMeasure m (cheegerHeat h t v))
    {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (2*K*b)*quadraticWassersteinSq (μ b:Measure X) (ν b:Measure X) ≤
      quadraticWassersteinSq (μ 0:Measure X) (ν 0:Measure X) := by
  sorry
end WeakHessian

end
end InlinedFile73

end OAI
end
