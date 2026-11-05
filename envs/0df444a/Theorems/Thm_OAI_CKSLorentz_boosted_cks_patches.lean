-- Prove2me | Theorems.Thm_OAI_CKSLorentz_boosted_cks_patches
-- name    : OAI.CKSLorentz.boosted_cks_patches
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:50.16402+00:00
-- url     : https://prove2.me/theorems/6b65fd16-8111-4037-bc64-1d86a0a41783
-- title:
--   Lorentz boosts carry CKS patches to CKS patches
-- statement:
--   Let $\|p\|<e$, let $A,B$ be spatial tensors and let `old` assign to each $n\in S^2$ a CKS tensor patch containing $n$, realizing $(A,B)$ and representing the mass aspect $M$. Then there is a family `new` of CKS tensor patches, each containing its direction $n$, realizing the pullbacks of $A,B$ by the boosted hyperbolic map, and representing the pulled-back mass aspect `aspectPullback e p he M`, which is $M$ at the boosted boundary point times the inverse cube of the boost denominator.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem boosted_cks_patches {M : Sphere → ℝ} {e : ℝ} {p : E} (he : ‖p‖ < e)
--       (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
--       (hcovers : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
--       (hreal : ∀ n, (old n).Realizes A B) (hrep : ∀ n, (old n).RepresentsMassAspect M) :
--       ∃ new : Sphere → CKSTensorPatch,
--         (∀ n, n ∈ (new n).patch.sphereRegion (new n).region) ∧
--         (∀ n, (new n).Realizes (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
--           (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)) ∧
--         (∀ n, (new n).RepresentsMassAspect (aspectPullback e p he M))
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/SourceBalancedPatches.lean`, lines 48-72, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/SourceBalancedPatches.lean#L48-L72 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem boosted_cks_patches {M : Sphere → ℝ} {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hcovers : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hreal : ∀ n, (old n).Realizes A B) (hrep : ∀ n, (old n).RepresentsMassAspect M) :
    ∃ new : Sphere → CKSTensorPatch,
      (∀ n, n ∈ (new n).patch.sphereRegion (new n).region) ∧
      (∀ n, (new n).Realizes (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
        (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)) ∧
      (∀ n, (new n).RepresentsMassAspect (aspectPullback e p he M)) := by
  sorry

end
end CKSLorentz
end
end OAI
