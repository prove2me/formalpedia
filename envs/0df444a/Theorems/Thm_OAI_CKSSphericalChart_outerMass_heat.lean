-- Prove2me | Theorems.Thm_OAI_CKSSphericalChart_outerMass_heat
-- name    : OAI.CKSSphericalChart.outerMass_heat
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:38:33.25839+00:00
-- url     : https://prove2.me/theorems/2ce96ed1-9aa4-411f-af06-de64a1043125
-- title:
--   The radial heat equation for the outer mass
-- statement:
--   For $f_0$ smooth on $S^2$, $m\in\mathbb R$, $R>0$ and a chart point $x=(r,\theta,\varphi)$ with $r\ge 3R$ and $\sin\theta\ne 0$, the function $F=$ `outerMass f₀ m R` satisfies
--   $$\partial_r F=\frac{\zeta_R(r)\,\Delta_{S^2}F}{2r\,(1+v_R(r)^2)}+\frac{1}{r\sqrt r},$$
--   where $\zeta_R=$ `bendingZeta R`, $v_R=$ `bendingV R`, and $\Delta_{S^2}F$ is the sphere Laplacian computed from the mass jet in the chart.
--
--   The last term is the padding density. The heat term cancels the Laplacian term that the mass aspect would otherwise contribute to the energy.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem outerMass_heat (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
--       {R : ℝ} (hR : 0 < R) {x : Point} (hr : 3*R ≤ x 0) (hs : Real.sin (x 1) ≠ 0) :
--       D (basis 0) (outerMass f₀ m R) x =
--         bendingZeta R (x 0) * (massJet (outerMass f₀ m R) x).laplace
--           (Real.sin (x 1)) (Real.cos (x 1)) / (2*x 0*A (bendingV R (x 0))) +
--         1/(x 0*Real.sqrt (x 0))
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/HeatRadial.lean`, lines 75-91, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/HeatRadial.lean#L75-L91 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

theorem outerMass_heat (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : Point} (hr : 3*R ≤ x 0) (hs : Real.sin (x 1) ≠ 0) :
    D (basis 0) (outerMass f₀ m R) x =
      bendingZeta R (x 0) * (massJet (outerMass f₀ m R) x).laplace
        (Real.sin (x 1)) (Real.cos (x 1)) / (2*x 0*A (bendingV R (x 0))) +
      1/(x 0*Real.sqrt (x 0)) := by
  sorry

end
end CKSSphericalChart
end
end OAI
