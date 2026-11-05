-- Prove2me | Theorems.Thm_OAI_CKSMixedGeometry_source_actual_collar_future_regions
-- name    : OAI.CKSMixedGeometry.source_actual_collar_future_regions
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:40:16.401209+00:00
-- url     : https://prove2.me/theorems/a6844055-ebb0-4310-aa25-7427bbf5f4d4
-- title:
--   Positivity of the collar's future-region quantities
-- statement:
--   Let $K$ be a compact set of positive-definite three-jets and $B\ge 0$. There is $R_0\ge 1$ such that for all $R\ge R_0$, source tensor fields $f$ and $(\rho,x)$ with $R\le e^\rho\le 3R$, under smoothness, positivity and the jet and component bounds with constant $B$, both the collar data with parameters $b=$ `collarParams R (exp ρ)` and the original data with parameters `oldParams b` satisfy: the angular matrix is positive (`positiveAngular`), and the two lapse quantities `lapseRadField` and `lapseDField` are positive.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem source_actual_collar_future_regions {K : Set MatrixThreeJet} (hK : IsCompact K)
--       (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
--       {B : ℝ} (hB : 0 ≤ B) :
--       ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
--         R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
--         f.SmoothAt (logRadiusChart (slice ρ x)) →
--         (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
--         matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
--         ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
--         ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
--         ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
--         ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
--         f.ComponentBounds B (logRadiusChart (slice ρ x)) →
--         let b := collarParams R (Real.exp ρ)
--         let c := (sourceCollarData f.logFields).angular ρ
--         (positiveAngular (fieldQ b c x) ∧
--           0 < lapseRadField (b 0) (fieldT b c) (fieldF b c) x ∧
--           0 < lapseDField (b 0) (fieldD b c) x) ∧
--         (positiveAngular (fieldQ (oldParams b) c x) ∧
--           0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) c) (fieldF (oldParams b) c) x ∧
--           0 < lapseDField ((oldParams b) 0) (fieldD (oldParams b) c) x)
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/BondiBalance.lean`, lines 878-911, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/BondiBalance.lean#L878-L911 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

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

theorem source_actual_collar_future_regions {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.SmoothAt (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      let b := collarParams R (Real.exp ρ)
      let c := (sourceCollarData f.logFields).angular ρ
      (positiveAngular (fieldQ b c x) ∧
        0 < lapseRadField (b 0) (fieldT b c) (fieldF b c) x ∧
        0 < lapseDField (b 0) (fieldD b c) x) ∧
      (positiveAngular (fieldQ (oldParams b) c x) ∧
        0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) c) (fieldF (oldParams b) c) x ∧
        0 < lapseDField ((oldParams b) 0) (fieldD (oldParams b) c) x) := by
  sorry

end
end CKSMixedGeometry
end
end OAI
