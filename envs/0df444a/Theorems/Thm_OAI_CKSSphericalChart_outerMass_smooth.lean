-- Prove2me | Theorems.Thm_OAI_CKSSphericalChart_outerMass_smooth
-- name    : OAI.CKSSphericalChart.outerMass_smooth
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:38:26.081201+00:00
-- url     : https://prove2.me/theorems/f9a4b131-30e5-4073-9577-fc5348618425
-- title:
--   Smoothness of the outer mass function on the positive radial chart
-- statement:
--   For a smooth function $f_0$ on $S^2$ and $m\in\mathbb R$ and $R>0$, the function $$F(r,\theta,\varphi)=c_R(r)+\Big(m+\big(\text{heat evolution of }f_0\big)\big(t_R(r),\,\omega(\theta,\varphi)\big)\Big),$$ where $c_R$ is the padding mass `paddingMass R` and $t_R$ is the heat time `heatTime R` is $C^\infty$ on the chart $\{x: x_0>0\}$ of radius and angle coordinates.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem outerMass_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) {R : ℝ} (hR : 0 < R) :
--       ContDiffOn ℝ ∞ (outerMass f₀ m R) positiveChart
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/HeatRadial.lean`, lines 65-67, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/HeatRadial.lean#L65-L67 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

theorem outerMass_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (outerMass f₀ m R) positiveChart := by
  sorry

end
end CKSSphericalChart
end
end OAI
