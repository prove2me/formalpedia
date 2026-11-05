-- Prove2me | Theorems.Thm_OAI_CKSMixedGeometry_cks_sourceCollarData_bounded
-- name    : OAI.CKSMixedGeometry.cks_sourceCollarData_bounded
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:05.657667+00:00
-- url     : https://prove2.me/theorems/6b240572-927e-4e0f-8002-1ea16b60a734
-- title:
--   Uniform bounds for the collar data extracted from CKS tensor fields
-- statement:
--   Let $K$ be a compact set of matrix three-jets with invertible value matrices and let $B\ge 0$. There are $R_0\ge 1$ and $C\ge 0$ such that, for all tensor fields $f$ in logarithmic radial coordinates and points $x$ with $e^{x_0}\ge R_0$, if $f$ is regular at $x$, its logarithmic metric is positive definite near $x$, the three-jet of the angular metric $\sigma$ at $x$ lies in $K$, and the component bounds `LogComponentBound B` hold at $x$, then the collar data `sourceCollarData f` satisfy `BoundedAt C` at $x$. The log component bounds have the CKS decay weights, for example the error of the angular metric is $O(e^{-2x_0})$, the shift is $O(e^{-3x_0})$ and the radial error is $O(e^{-6x_0})$.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem cks_sourceCollarData_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
--       (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
--       {B : ℝ} (hB : 0 ≤ B) :
--       ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : TensorFields, ∀ x : Point,
--         R₀ ≤ Real.exp (x 0) → f.RegularAt x →
--         (∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) → matrixThreeJets f.base.sigma x ∈ K →
--         f.LogComponentBound B x → (sourceCollarData f).BoundedAt C x
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/CKSCollarSourceData.lean`, lines 47-93, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/CKSCollarSourceData.lean#L47-L93 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem cks_sourceCollarData_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : TensorFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) → matrixThreeJets f.base.sigma x ∈ K →
      f.LogComponentBound B x → (sourceCollarData f).BoundedAt C x := by
  sorry

end
end CKSMixedGeometry
end
end OAI
