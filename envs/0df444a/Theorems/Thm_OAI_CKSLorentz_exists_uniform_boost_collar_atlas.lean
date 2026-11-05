-- Prove2me | Theorems.Thm_OAI_CKSLorentz_exists_uniform_boost_collar_atlas
-- name    : OAI.CKSLorentz.exists_uniform_boost_collar_atlas
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:10.986947+00:00
-- url     : https://prove2.me/theorems/171e6ecc-24e6-4680-9ad2-75bc2bc2394c
-- title:
--   A finite boosted atlas with uniform collar inputs
-- statement:
--   Let $\|p\|<e$, let $A,B$ be spatial tensor fields and let `old` assign to each direction $n\in S^2$ a CKS tensor patch containing $n$ in its region and realizing $(A,B)$. Then there are a finite set $s\subset S^2$, angular patches $P_n$, radii $\delta_n$, a radius $R>0$, a compact set $K$ of positive-definite three-jets and a constant $C\ge 0$ such that for each $n\in s$ the boosted fields form a `SpatialBoostPatch` on the ball of radius $2\delta_n$, they satisfy `UniformCollarInput K C R` on the closed ball of radius $\delta_n$ around the chart image of $n$, and these balls, pulled back to the sphere, cover $S^2$.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem exists_uniform_boost_collar_atlas {e : ℝ} {p : E} (he : ‖p‖ < e)
--       (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
--       (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
--       (hreal : ∀ n, (old n).Realizes A B) :
--       ∃ (s : Finset Sphere) (P : Sphere → SmoothAngularPatch) (δ : Sphere → ℝ)
--         (R : ℝ) (K : Set MatrixThreeJet) (C : ℝ),
--         0 < R ∧ IsCompact K ∧
--         (∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1)) ∧ 0 ≤ C ∧
--         (∀ n ∈ s, SpatialBoostPatch e p he A B (old (boundary e p he n))
--           (P n) ((P n).chart n) (2*δ n) R) ∧
--         (∀ n ∈ s, (boostSourceFields e p A B (old (boundary e p he n)) (P n)).UniformCollarInput
--           K C R (Metric.closedBall ((P n).chart n) (δ n))) ∧
--         (∀ q : Sphere, ∃ n ∈ s, q ∈ (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n)))
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/ConstructedOuterMetric.lean`, lines 5086-5120, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/ConstructedOuterMetric.lean#L5086-L5120 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology Matrix

end
end CKSSphericalChart

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice
open scoped ContDiff

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

namespace FiniteLogDecay
variable {j : ℕ} {q r : ℝ} {U : Set Point} {f g : Point → ℝ}

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff
namespace FiniteLogDecay

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set
open scoped ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set
open scoped ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus CKSAngularSlice
open scoped ContDiff Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
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
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

namespace SmoothAngularPatch

end SmoothAngularPatch

attribute [local instance] stereoDimension

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

attribute [local instance] stereoDimension

namespace SmoothAngularPatch

end SmoothAngularPatch
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
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
open CKSMixedGeometry CKSAngularSlice
attribute [local instance] real_continuousAdd

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
namespace CKSMixedGeometry
noncomputable section
open CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

end SmoothAngularPatch

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped Topology ContDiff

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open Set

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
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Set

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
open CKSMixedGeometry CKSAngularSlice Set
open scoped Topology ContDiff

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry
open CKSAngularGeometry (metricBlock AmbientMat)

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Set
open CKSAngularGeometry (metricBlock AmbientMat)

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
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set CKSAngularSlice CKSCalculus
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open scoped Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set CKSAngularSlice
open scoped Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped Matrix.Norms.Elementwise

theorem exists_uniform_boost_collar_atlas {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hreal : ∀ n, (old n).Realizes A B) :
    ∃ (s : Finset Sphere) (P : Sphere → SmoothAngularPatch) (δ : Sphere → ℝ)
      (R : ℝ) (K : Set MatrixThreeJet) (C : ℝ),
      0 < R ∧ IsCompact K ∧
      (∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1)) ∧ 0 ≤ C ∧
      (∀ n ∈ s, SpatialBoostPatch e p he A B (old (boundary e p he n))
        (P n) ((P n).chart n) (2*δ n) R) ∧
      (∀ n ∈ s, (boostSourceFields e p A B (old (boundary e p he n)) (P n)).UniformCollarInput
        K C R (Metric.closedBall ((P n).chart n) (δ n))) ∧
      (∀ q : Sphere, ∃ n ∈ s, q ∈ (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n))) := by
  sorry

end
end CKSLorentz
end
end OAI
