-- Prove2me | Theorems.Thm_OAI_CKSMixedGeometry_source_collar_metric_comparison
-- name    : OAI.CKSMixedGeometry.source_collar_metric_comparison
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:16.44762+00:00
-- url     : https://prove2.me/theorems/9f0f4ddd-e965-4e5d-a58f-dda10bd23519
-- title:
--   A lower metric comparison on the collar
-- statement:
--   Let $K$ be a compact set of positive-definite three-jets and $B\ge 0$. There are $R_0\ge 1$ and a function $l$ with $l(R)\to 1$ as $R\to\infty$ and $0\le l(R)\le 1$ for $R\ge R_0$, such that for all $R\ge R_0$, source tensor fields $f$, $(\rho,x)$ with $R\le e^\rho\le 3R$ such that $f$ is regular at the point with radius $e^\rho$ and angle $x$, `f.base.mK` and `f.base.ek` are $C^3$ there, the source metric is positive definite nearby, the angular jet lies in $K$, and the jets of $\sigma,m^g,m^K,m^r$ and the components of $f$ obey the bounds with constant $B$, and all $v\in\mathbb R^3$,
--   $$l(R)\,\mathcal Q_{\mathrm{orig}}(v)\le\mathcal Q_{\mathrm{collar}}(v),$$
--   where $\mathcal Q_{\mathrm{orig}}$ is the quadratic form of the radially normalized source metric and $\mathcal Q_{\mathrm{collar}}$ that of the normalized collar metric with parameters `collarParams R (exp ρ)`.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem source_collar_metric_comparison {K : Set MatrixThreeJet} (hK : IsCompact K)
--       (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
--       {B : ℝ} (hB : 0 ≤ B) :
--       ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
--         (∀ R, R₀ ≤ R → 0 ≤ l R ∧ l R ≤ 1) ∧
--         ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
--         R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
--         f.RegularAt (logRadiusChart (slice ρ x)) →
--         ContDiffAt ℝ 3 f.base.mK (angularProjection (logRadiusChart (slice ρ x))) →
--         ContDiffAt ℝ 3 f.base.ek (logRadiusChart (slice ρ x)) →
--         (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
--         matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
--         ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
--         ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
--         ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
--         ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
--         f.ComponentBounds B (logRadiusChart (slice ρ x)) →
--         ∀ v : Fin 3 → ℝ,
--         l R * CKSAngularGeometry.quadratic3
--           (CKSAngularGeometry.radialNormalize (Real.exp ρ) (sourceMetric f.base (logRadiusChart (slice ρ x)))) v ≤
--         CKSAngularGeometry.quadratic3
--           (CKSAngularGeometry.fieldNormalizedMetric (CKSBending.collarParams R (Real.exp ρ))
--             ((sourceCollarData f.logFields).angular ρ) x) v
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/BondiBalance.lean`, lines 1723-1782, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/BondiBalance.lean#L1723-L1782 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

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
attribute [local instance] OAI.CKSLorentz.globalCollarEeNorm
attribute [local instance] OAI.CKSLorentz.globalCollarEeSpace

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Matrix
open CKSAngularGeometry (metricBlock AmbientMat)

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem source_collar_metric_comparison {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R, R₀ ≤ R → 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.RegularAt (logRadiusChart (slice ρ x)) →
      ContDiffAt ℝ 3 f.base.mK (angularProjection (logRadiusChart (slice ρ x))) →
      ContDiffAt ℝ 3 f.base.ek (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      ∀ v : Fin 3 → ℝ,
      l R * CKSAngularGeometry.quadratic3
        (CKSAngularGeometry.radialNormalize (Real.exp ρ) (sourceMetric f.base (logRadiusChart (slice ρ x)))) v ≤
      CKSAngularGeometry.quadratic3
        (CKSAngularGeometry.fieldNormalizedMetric (CKSBending.collarParams R (Real.exp ρ))
          ((sourceCollarData f.logFields).angular ρ) x) v := by
  sorry

end
end CKSMixedGeometry
end
end OAI
