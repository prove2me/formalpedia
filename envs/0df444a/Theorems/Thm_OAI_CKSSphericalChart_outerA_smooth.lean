-- Prove2me | Theorems.Thm_OAI_CKSSphericalChart_outerA_smooth
-- name    : OAI.CKSSphericalChart.outerA_smooth
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:11.082956+00:00
-- url     : https://prove2.me/theorems/03be169d-64f8-435d-ae09-259185e0447d
-- title:
--   Smoothness of the outer tensor component on the positive radial chart
-- statement:
--   For a smooth function $f_0$ on $S^2$ and $R>0$, the function `outerA f₀ R`, which evaluates the heat tensor `canonicalT f₀` of $f_0$ at time $t_R(r)$, with $t_R=$ `heatTime R`, on the pair (theta frame, theta frame) is $C^\infty$ on the chart $\{x: x_0>0\}$ of radius and angle coordinates.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem outerA_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) {R : ℝ} (hR : 0 < R) :
--       ContDiffOn ℝ ∞ (outerA f₀ R) positiveChart
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/HeatRadial.lean`, lines 68-70, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/HeatRadial.lean#L68-L70 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

theorem outerA_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (outerA f₀ R) positiveChart := by
  sorry

end
end CKSSphericalChart
end
end OAI
