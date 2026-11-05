-- Prove2me | Theorems.Thm_OAI_CKSLorentz_actual_same_end_smooth_replacement
-- name    : OAI.CKSLorentz.actual_same_end_smooth_replacement
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:37.35868+00:00
-- url     : https://prove2.me/theorems/b6ea4791-3a88-40b6-8b7f-d432d3dafaae
-- title:
--   Smoothness, positivity and localization of the replacement
-- statement:
--   Here `A`, `B` are the perturbations of the hyperbolic metric field and of the second tensor, `sourceSpatial A` is the hyperbolic field plus `A`, and a `SourceCollarAtlas A B ι` is a family of angular coordinate patches of the sphere, covering the sphere, together with a common radius, a compact set of positive-definite angular jets and a common bound giving uniform collar inputs on every patch, with the source fields smooth, the source metric positive definite, the source second tensor symmetric and `physicalDEC` holding for the source data on the tail of each patch beyond that radius. Under the hypotheses of the mass aspect $M$ with `bondiCharge M = (m,0)` and symmetry of $A,B$ outside `q.radius`, there are $S\ge 1$ and $R_0$ with `q.radius` $<S<R_0$ such that for every $R\ge R_0$ the replacement metric and tensor are $C^\infty$ on $\{\|x\|>S\}$, with symmetric metric, positive-definite metric and symmetric tensor there. In addition, they equal the source for $\|x\|\le R$, they equal the outer data for $\|x\|>3R$, and on the collar they satisfy `physicalDEC` with the collar frame, in polar components.
--
--   `q.replacementMetric f₀ m R` equals `sourceSpatial A` for $\|x\|\le R$, the collar metric of the atlas for $R<\|x\|\le 3R$, and the Cartesian outer metric for $\|x\|>3R$; `q.replacementTensor f₀ m R` is defined the same way. In this statement $M$ is a smooth function on $S^2$ with `q.HasMassAspect M`, and $f_0=$ `heatDatum M hM`, the function $M/4$. In this statement $M$ is a smooth function on $S^2$ with `q.HasMassAspect M`, and $f_0=$ `heatDatum M hM`, the function $M/4$.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem actual_same_end_smooth_replacement {A B : SpatialTensor} {ι : Type*}
--       (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
--       (hmass : q.HasMassAspect M) (m : ℝ) (hcharge : bondiCharge M = (m,0))
--       (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
--       (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
--       ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧
--         ∀ R ≥ R₀,
--           ContDiffOn ℝ ∞ (q.replacementMetric (heatDatum M hM) m R) {x | S < ‖x‖} ∧
--           ContDiffOn ℝ ∞ (q.replacementTensor (heatDatum M hM) m R) {x | S < ‖x‖} ∧
--           (∀ x, S < ‖x‖ →
--             (∀ v w, q.replacementMetric (heatDatum M hM) m R x v w =
--               q.replacementMetric (heatDatum M hM) m R x w v) ∧
--             (∀ v : E, v ≠ 0 → 0 < q.replacementMetric (heatDatum M hM) m R x v v) ∧
--             ∀ v w, q.replacementTensor (heatDatum M hM) m R x v w =
--               q.replacementTensor (heatDatum M hM) m R x w v) ∧
--           (∀ x, ‖x‖ ≤ R →
--             q.replacementMetric (heatDatum M hM) m R x = sourceSpatial A x ∧
--             q.replacementTensor (heatDatum M hM) m R x = sourceSpatial B x) ∧
--           (∀ x, 3*R < ‖x‖ →
--             q.replacementMetric (heatDatum M hM) m R x =
--               spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) x ∧
--             q.replacementTensor (heatDatum M hM) m R x =
--               spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) x) ∧
--           ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
--             physicalDEC (fun z => fun a b => polarTensorComponents (q.patch i).patch
--                 (q.replacementMetric (heatDatum M hM) m R) a b z)
--               (fun z => fun a b => polarTensorComponents (q.patch i).patch
--                 (q.replacementTensor (heatDatum M hM) m R) a b z)
--               (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/TailEnergy.lean`, lines 3215-3348, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/TailEnergy.lean#L3215-L3348 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

namespace CKSSpatialManifold

end CKSSpatialManifold

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRound CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

end
end CKSSphericalChart

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open Matrix CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSRealizedRound

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSAngularGeometry CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise Matrix

end
end CKSSphericalChart

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSSphericalChart

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set CKSSphericalChart CKSRealizedRound
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSBending
noncomputable section
open Set
open scoped Topology ContDiff

end
end CKSBending

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSBending Set
open scoped ContDiff

end
end CKSAngularSlice

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Matrix Set Filter CKSCalculus CKSRealizedRound CKSAngularGeometry CKSAngularSlice CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSSphericalChart

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSAngularGeometry CKSAngularSlice CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSSphericalChart

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSTangentCoefficients

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSCalculus Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSTangentCoefficients CKSCartesianOuter CKSInducedSphere CKSSphericalChart
open scoped BigOperators

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
open scoped Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
  CKSADM CKSBending CKSSphericalHarmonics CKSInducedSphere
open CKSRealizedRound (correctionCoeff)
open scoped Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
  CKSSphericalHarmonics CKSBending Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Filter
open scoped Topology ContDiff

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
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients
open scoped ContDiff Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.smrbilNorm
attribute [local instance] OAI.CKSLorentz.smrbilSpace
attribute [local instance] OAI.CKSLorentz.smrepNorm
attribute [local instance] OAI.CKSLorentz.smrepSpace
attribute [local instance] OAI.CKSLorentz.smrpeNorm
attribute [local instance] OAI.CKSLorentz.smrpeSpace
attribute [local instance] OAI.CKSLorentz.smreeNorm
attribute [local instance] OAI.CKSLorentz.smreeSpace

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularGeometry
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

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
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology

theorem actual_same_end_smooth_replacement {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hmass : q.HasMassAspect M) (m : ℝ) (hcharge : bondiCharge M = (m,0))
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧
      ∀ R ≥ R₀,
        ContDiffOn ℝ ∞ (q.replacementMetric (heatDatum M hM) m R) {x | S < ‖x‖} ∧
        ContDiffOn ℝ ∞ (q.replacementTensor (heatDatum M hM) m R) {x | S < ‖x‖} ∧
        (∀ x, S < ‖x‖ →
          (∀ v w, q.replacementMetric (heatDatum M hM) m R x v w =
            q.replacementMetric (heatDatum M hM) m R x w v) ∧
          (∀ v : E, v ≠ 0 → 0 < q.replacementMetric (heatDatum M hM) m R x v v) ∧
          ∀ v w, q.replacementTensor (heatDatum M hM) m R x v w =
            q.replacementTensor (heatDatum M hM) m R x w v) ∧
        (∀ x, ‖x‖ ≤ R →
          q.replacementMetric (heatDatum M hM) m R x = sourceSpatial A x ∧
          q.replacementTensor (heatDatum M hM) m R x = sourceSpatial B x) ∧
        (∀ x, 3*R < ‖x‖ →
          q.replacementMetric (heatDatum M hM) m R x =
            spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) x ∧
          q.replacementTensor (heatDatum M hM) m R x =
            spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) x) ∧
        ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
          physicalDEC (fun z => fun a b => polarTensorComponents (q.patch i).patch
              (q.replacementMetric (heatDatum M hM) m R) a b z)
            (fun z => fun a b => polarTensorComponents (q.patch i).patch
              (q.replacementTensor (heatDatum M hM) m R) a b z)
            (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y := by
  sorry

end
end CKSLorentz
end
end OAI
