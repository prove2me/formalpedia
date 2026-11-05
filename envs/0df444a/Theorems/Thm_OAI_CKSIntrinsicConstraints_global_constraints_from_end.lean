-- Prove2me | Theorems.Thm_OAI_CKSIntrinsicConstraints_global_constraints_from_end
-- name    : OAI.CKSIntrinsicConstraints.global_constraints_from_end
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:40:04.94143+00:00
-- url     : https://prove2.me/theorems/43bb416f-85f9-47f0-a2bb-9820b25fc776
-- title:
--   Global integrable constraint densities from integrability on the end
-- statement:
--   Let $(M,g,K)$ satisfy the physical DEC, with an end chart $f$ on an open set $V$ and smooth inverse on $\{\|y\|>T\}$, and suppose $T<s$ and $\{x: x\notin V\text{ or }\|f(x)\|\le s\}$ is compact. Assume $g,K$ are represented on $V$ by smooth tensors $A,B$ on $\{\|y\|>T\}$, with $A$ symmetric positive definite and $B$ symmetric, and that the energy density and momentum norm of $(A,B)$ are integrable over $\{\|y\|>s\}$ against the volume of $A$. Then there are continuous functions $C,Q$ on $M$, integrable for the Riemannian volume of $g$, with $0\le Q\le C$, which at every point agree with the energy and momentum norm of any constraint chart.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem global_constraints_from_end
--       (g : SmoothMetric I (M := M)) (K : InnerField I (M := M))
--       (hDEC : PhysicalDEC I g.inner K)
--       (f : M → E) (finv : E → M) {V : Set M} {T s : ℝ}
--       (hs : T < s) (hV : IsOpen V)
--       (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ f V)
--       (hi : ContMDiffOn 𝓘(ℝ,E) I ∞ finv {y | T < ‖y‖})
--       (hleft : ∀ x ∈ V, finv (f x) = x)
--       (hright : ∀ y, T < ‖y‖ → finv y ∈ V ∧ f (finv y) = y)
--       (hcompact : IsCompact {x : M | x ∉ V ∨ ‖f x‖ ≤ s})
--       (A B : SpatialTensor)
--       (hAs : ContDiffOn ℝ ∞ A {y | T < ‖y‖})
--       (hBs : ContDiffOn ℝ ∞ B {y | T < ‖y‖})
--       (hA : ∀ y, T < ‖y‖ →
--         (∀ v w, A y v w = A y w v) ∧ (∀ v : E, v ≠ 0 → 0 < A y v v))
--       (hB : ∀ y, T < ‖y‖ → ∀ v w, B y v w = B y w v)
--       (hrep : ∀ x ∈ V, g.inner x = endInner I f A x ∧ K x = endInner I f B x)
--       (hCint : IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion s) (spatialVolume A))
--       (hQint : IntegrableOn (coordinateMomentumNorm A B) (CKSTailVolume.tailRegion s) (spatialVolume A)) :
--       ∃ C Q : M → ℝ, Continuous C ∧ Continuous Q ∧
--         Integrable C (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
--         Integrable Q (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
--         (∀ x, 0 ≤ Q x ∧ Q x ≤ C x) ∧
--         ∀ x (c : ConstraintChart g.inner K x), C x = c.energy ∧ Q x = c.momentumNorm
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/IntrinsicEndChart.lean`, lines 37-74, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/IntrinsicEndChart.lean#L37-L74 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

theorem global_constraints_from_end
    (g : SmoothMetric I (M := M)) (K : InnerField I (M := M))
    (hDEC : PhysicalDEC I g.inner K)
    (f : M → E) (finv : E → M) {V : Set M} {T s : ℝ}
    (hs : T < s) (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ f V)
    (hi : ContMDiffOn 𝓘(ℝ,E) I ∞ finv {y | T < ‖y‖})
    (hleft : ∀ x ∈ V, finv (f x) = x)
    (hright : ∀ y, T < ‖y‖ → finv y ∈ V ∧ f (finv y) = y)
    (hcompact : IsCompact {x : M | x ∉ V ∨ ‖f x‖ ≤ s})
    (A B : SpatialTensor)
    (hAs : ContDiffOn ℝ ∞ A {y | T < ‖y‖})
    (hBs : ContDiffOn ℝ ∞ B {y | T < ‖y‖})
    (hA : ∀ y, T < ‖y‖ →
      (∀ v w, A y v w = A y w v) ∧ (∀ v : E, v ≠ 0 → 0 < A y v v))
    (hB : ∀ y, T < ‖y‖ → ∀ v w, B y v w = B y w v)
    (hrep : ∀ x ∈ V, g.inner x = endInner I f A x ∧ K x = endInner I f B x)
    (hCint : IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion s) (spatialVolume A))
    (hQint : IntegrableOn (coordinateMomentumNorm A B) (CKSTailVolume.tailRegion s) (spatialVolume A)) :
    ∃ C Q : M → ℝ, Continuous C ∧ Continuous Q ∧
      Integrable C (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      Integrable Q (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      (∀ x, 0 ≤ Q x ∧ Q x ≤ C x) ∧
      ∀ x (c : ConstraintChart g.inner K x), C x = c.energy ∧ Q x = c.momentumNorm := by
  sorry

end CKSIntrinsicConstraints
end
end OAI
