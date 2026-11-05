-- Prove2me | Theorems.Thm_OAI_CKSLorentz_SourceCollarAtlas_eventually_pointwise
-- name    : OAI.CKSLorentz.SourceCollarAtlas.eventually_pointwise
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:21.82811+00:00
-- url     : https://prove2.me/theorems/0b7d2a49-be99-428c-98b4-b3c48482fae4
-- title:
--   Regularity and DEC of the collar for all large radii
-- statement:
--   Here `A`, `B` are the perturbations of the hyperbolic metric field and of the second tensor, `sourceSpatial A` is the hyperbolic field plus `A`, and a `SourceCollarAtlas A B ι` is a family of angular coordinate patches of the sphere, covering the sphere, together with a common radius, a compact set of positive-definite angular jets and a common bound giving uniform collar inputs on every patch, with the source fields smooth, the source metric positive definite, the source second tensor symmetric and `physicalDEC` holding for the source data on the tail of each patch beyond that radius. For every atlas `q` there is $R_0\ge 1$ with $R_0>$ `q.radius` such that for all $R\ge R_0$, every patch $i$ and every point $y$ with $R\le y_0\le 3R$ and angle in the region of patch $i$: the collar metric and tensor of patch $i$ are regular at $y$ (`PhysicalRegularAt`) and satisfy `physicalDEC` with the collar frame at $y$.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem SourceCollarAtlas.eventually_pointwise {A B : SpatialTensor} {ι : Type*}
--       (q : SourceCollarAtlas A B ι) :
--       ∃ R₀ : ℝ, 1 ≤ R₀ ∧ q.radius < R₀ ∧ ∀ R ≥ R₀, ∀ i y,
--         R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
--         PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
--           (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y ∧
--         physicalDEC (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
--           (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields))
--           (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/BondiBalance.lean`, lines 1429-1469, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/BondiBalance.lean#L1429-L1469 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure Balanced sphereIntegral sphereArea)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMetricGluing
noncomputable section
open Bundle Manifold Set Bornology
open scoped Bundle Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] real_continuousAdd

variable {I}

end
end CKSMetricGluing

end

noncomputable section
namespace CKSMetricGluing
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

end
end CKSMetricGluing

end

noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators

variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] OAI.CKSTangentCoefficients.scalarAtlas

end
end CKSTangentCoefficients

end

noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators Topology

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] scalarAtlas

end
end CKSTangentCoefficients

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped BigOperators

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set CKSAngularGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
open scoped BigOperators

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped ContDiff Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.bilNorm
attribute [local instance] OAI.CKSLorentz.bilSpace
attribute [local instance] OAI.CKSLorentz.epNorm
attribute [local instance] OAI.CKSLorentz.epSpace
attribute [local instance] OAI.CKSLorentz.peNorm
attribute [local instance] OAI.CKSLorentz.peSpace
attribute [local instance] OAI.CKSLorentz.eeNorm
attribute [local instance] OAI.CKSLorentz.eeSpace

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem SourceCollarAtlas.eventually_pointwise {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ q.radius < R₀ ∧ ∀ R ≥ R₀, ∀ i y,
      R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y ∧
      physicalDEC (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y := by
  sorry

end
end CKSLorentz
end
end OAI
