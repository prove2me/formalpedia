-- Prove2me | Theorems.Thm_OAI_CKSLorentz_actual_same_end_DEC
-- name    : OAI.CKSLorentz.actual_same_end_DEC
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:49.492931+00:00
-- url     : https://prove2.me/theorems/1b00409e-7cee-4bc4-a54c-f803103a67f1
-- title:
--   DEC of the replacement on the whole end
-- statement:
--   Here `A`, `B` are the perturbations of the hyperbolic metric field and of the second tensor, `sourceSpatial A` is the hyperbolic field plus `A`, and a `SourceCollarAtlas A B ι` is a family of angular coordinate patches of the sphere, covering the sphere, together with a common radius, a compact set of positive-definite angular jets and a common bound giving uniform collar inputs on every patch, with the source fields smooth, the source metric positive definite, the source second tensor symmetric and `physicalDEC` holding for the source data on the tail of each patch beyond that radius. Under the mass-aspect hypotheses, with `bondiCharge M = (m,0)` and symmetric $A,B$ outside `q.radius`, there are $S\ge 1$ and $R_0$ with `q.radius` $<S<R_0$ such that for all $R\ge R_0$ and $x$ with $\|x\|>S$, the replacement metric and tensor satisfy `spatialDEC` at $x$.
--
--   `q.replacementMetric f₀ m R` equals `sourceSpatial A` for $\|x\|\le R$, the collar metric of the atlas for $R<\|x\|\le 3R$, and the Cartesian outer metric for $\|x\|>3R$; `q.replacementTensor f₀ m R` is defined the same way. In this statement $M$ is a smooth function on $S^2$ with `q.HasMassAspect M`, and $f_0=$ `heatDatum M hM`, the function $M/4$.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem actual_same_end_DEC {A B : SpatialTensor} {ι : Type*}
--       (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
--       (hmass : q.HasMassAspect M) (m : ℝ) (hcharge : bondiCharge M = (m,0))
--       (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
--       (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
--       ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧
--         ∀ R ≥ R₀, ∀ x : E, S < ‖x‖ →
--           spatialDEC (q.replacementMetric (heatDatum M hM) m R)
--             (q.replacementTensor (heatDatum M hM) m R) x
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/TailEnergy.lean`, lines 4614-4680, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/TailEnergy.lean#L4614-L4680 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

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

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

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
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry
open scoped BigOperators

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
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise

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
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry
open scoped BigOperators

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry Matrix Set Filter
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.sgpNorm
attribute [local instance] OAI.CKSLorentz.sgpSpace

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] CKSSpatialManifold.real_id_isometric real_smulCommClass
  spatialDual_smulCommClass
attribute [local instance] OAI.CKSLorentz.hsgNorm

attribute [local instance] OAI.CKSLorentz.hsgSpace

attribute [local instance] spatialBilinear_isScalarTower

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
open Matrix

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
open CKSMixedGeometry CKSAngularSlice CKSCalculus

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
open CKSMixedGeometry CKSAngularSlice Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

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
open scoped ContDiff Topology

theorem actual_same_end_DEC {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hmass : q.HasMassAspect M) (m : ℝ) (hcharge : bondiCharge M = (m,0))
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧
      ∀ R ≥ R₀, ∀ x : E, S < ‖x‖ →
        spatialDEC (q.replacementMetric (heatDatum M hM) m R)
          (q.replacementTensor (heatDatum M hM) m R) x := by
  sorry

end
end CKSLorentz
end
end OAI
