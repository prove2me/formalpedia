-- Prove2me | Theorems.Thm_OAI_CKSSphericalChart_constructed_outer_DEC
-- name    : OAI.CKSSphericalChart.constructed_outer_DEC
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:38:40.253261+00:00
-- url     : https://prove2.me/theorems/11040aba-98a7-4e8c-ab40-32ce9837e1b6
-- title:
--   The dominant energy condition for the bent outer data
-- statement:
--   Here $f_0$ is a smooth function on the unit sphere $S^2$, $m$ a real number, and $R$ the replacement radius. There is $R_0\ge 12$ such that, for all $R\ge R_0$ and chart points with $r\ge 3R$ and $\sin\theta\ne 0$, the outer metric jet and tensor jet built from the lapse with mass $F=$ `outerMass f₀ m R` and bending profile $v_R=$ `bendingV R`, with second tensor determined by the normal entry $v_R'+\beta_R/r^2$, the trace part $v_R/r$ and the corrected components of $a,b$, satisfy the local inequality `DEC`.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem constructed_outer_DEC (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
--       ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : Point,
--       3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
--       DEC (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x)
--         (tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
--           (radial (normalEntry (bendingV R) (bendingBeta R)))
--           (correctedComponent (bendingV R) (outerA f₀ R))
--           (correctedComponent (bendingV R) (outerPhi f₀ R)) x)
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/OuterRealization.lean`, lines 11-45, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/OuterRealization.lean#L11-L45 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

theorem constructed_outer_DEC (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : Point,
    3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
    DEC (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x)
      (tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
        (radial (normalEntry (bendingV R) (bendingBeta R)))
        (correctedComponent (bendingV R) (outerA f₀ R))
        (correctedComponent (bendingV R) (outerPhi f₀ R)) x) := by
  sorry

end
end CKSSphericalChart
end
end OAI
