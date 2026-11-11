-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodge_residual_energy_zero
-- name    : OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:30.462643+00:00
-- url     : https://prove2.me/theorems/371d3508-0388-49d8-8fb6-27e2658b4fe9
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero` of [lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeResidualEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeResidualEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter`, `open scoped Manifold ContDiff RealInnerProductSpace Topology`):
--
--   ```lean
--   lemma hodge_residual_energy_zero
--       (μ ν : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--       (Q : L2 A J α hs ht true) (hQ : l2Star A J α hs ht Q = Q)
--       (hT : ∀ a : smoothForms X 2, IsClosed a.val →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
--       (hν : ∀ ξ : PreL2 A J α hs ht false,
--         (positiveL2Source A J α hs ht ν + l2CurrentSource A J α hs ht Q)
--           (hodgePreD A J α hs ht ξ) = 0)
--       (r : ℝ) (hr : 0 < r) :
--       let P := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ r
--       let P' := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) ν r
--       let V := hodgeRegularization A J α hs ht r Q
--       ⟪P,l2Star A J α hs ht P'⟫+⟪P,V⟫+⟪P',V⟫+‖V‖^2 = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.l2Star`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.hermitianMetric` and `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgePreD` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeRegularization`, `OAI.TamingCompatibility.GeometricHilbert.l2CurrentSource` and `OAI.TamingCompatibility.GeometricHilbert.positiveL2Source` (definitions bundle `OAIQ239Tc027` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgePositiveCurrentFamily` (definitions bundle `OAIQ239Tc032` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_forces_correction_zero` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeResidualEnergy.lean (declaration OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc032

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel

lemma hodge_residual_energy_zero
    (μ ν : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Q : L2 A J α hs ht true) (hQ : l2Star A J α hs ht Q = Q)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (hν : ∀ ξ : PreL2 A J α hs ht false,
      (positiveL2Source A J α hs ht ν + l2CurrentSource A J α hs ht Q)
        (hodgePreD A J α hs ht ξ) = 0)
    (r : ℝ) (hr : 0 < r) :
    let P := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ r
    let P' := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) ν r
    let V := hodgeRegularization A J α hs ht r Q
    ⟪P,l2Star A J α hs ht P'⟫+⟪P,V⟫+⟪P',V⟫+‖V‖^2 = 0 := by
  sorry
end TamingCompatibility.GeometricHilbert

end
end

end OAI
end
