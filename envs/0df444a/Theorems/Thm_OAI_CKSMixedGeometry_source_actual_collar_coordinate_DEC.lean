-- Prove2me | Theorems.Thm_OAI_CKSMixedGeometry_source_actual_collar_coordinate_DEC
-- name    : OAI.CKSMixedGeometry.source_actual_collar_coordinate_DEC
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:52.239918+00:00
-- url     : https://prove2.me/theorems/b1b841b3-8aca-41b8-bdff-c549f856fc62
-- title:
--   Coordinate DEC along the collar for actual source fields
-- statement:
--   Let $K$ be a compact set of matrix three-jets with positive-definite values and $B\ge 0$. There is $R_0\ge 1$ such that the following holds for all $R\ge R_0$, all source tensor fields $f$ and all log-radius and angle pairs $(\rho,x)$ with $R\le e^\rho\le 3R$. Assume $f$ is regular at the point with radius $e^\rho$ and angle $x$, `f.base.mK` and `f.base.ek` are $C^3$ there, the source metric is positive definite nearby, the angular jet lies in $K$, and the jets of $\sigma,m^g,m^K,m^r$ and the components of $f$ obey the bounds with constant $B$. If the coordinate DEC holds for the original data (`oldParams` of the collar parameters), then it holds for the collar data with parameters `collarParams R (exp ρ)`.
--
--   So on the whole collar $R\le r\le 3R$ the deformation by the rounding and padding weights preserves the coordinate DEC.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem source_actual_collar_coordinate_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
--       (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
--       {B : ℝ} (hB : 0 ≤ B) :
--       ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
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
--         CKSAngularGeometry.coordinateDEC
--           (CKSAngularGeometry.fieldNullInput
--             (CKSAngularGeometry.oldParams (CKSBending.collarParams R (Real.exp ρ)))
--             ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) →
--         CKSAngularGeometry.coordinateDEC
--           (CKSAngularGeometry.fieldNullInput (CKSBending.collarParams R (Real.exp ρ))
--             ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ)
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/SourceCollarBound.lean`, lines 33-64, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/SourceCollarBound.lean#L33-L64 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem source_actual_collar_coordinate_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
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
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput
          (CKSAngularGeometry.oldParams (CKSBending.collarParams R (Real.exp ρ)))
          ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSBending.collarParams R (Real.exp ρ))
          ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) := by
  sorry

end
end CKSMixedGeometry
end
end OAI
