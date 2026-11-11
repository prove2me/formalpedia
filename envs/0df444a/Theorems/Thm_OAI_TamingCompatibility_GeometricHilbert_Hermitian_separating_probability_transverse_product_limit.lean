-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_separating_probability_transverse_product_limit
-- name    : OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:15.88938+00:00
-- url     : https://prove2.me/theorems/884e74d0-820c-4626-9264-cbf3468c2ec3
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/UnitTransversePairProduct.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/UnitTransversePairProduct.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.Hermitian`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts`, `open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal`):
--
--   ```lean
--   lemma separating_probability_transverse_product_limit
--       (D : ∀ p : A.centers, Data J α ht p.val)
--       (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
--       (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
--       (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
--       (p : A.centers) {K : Set Space} (hK : IsCompact K)
--       (hKT : K ⊆ (extChartAt Model p.val).target) :
--       Tendsto (fun r : ℝ => ∫ uv, transversePairKernel A J α hs ht p K r uv ∂μ.prod μ)
--         (𝓝[>] (0:ℝ)) (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.hermitianMetric` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.Hermitian.transversePairKernel` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsInvariant`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_second_variation_limit` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_variation_limit` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/UnitTransversePairProduct.lean (declaration OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel

lemma separating_probability_transverse_product_limit
    (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ uv, transversePairKernel A J α hs ht p K r uv ∂μ.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  sorry
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end
