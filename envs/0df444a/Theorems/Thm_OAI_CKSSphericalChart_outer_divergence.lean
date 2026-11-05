-- Prove2me | Theorems.Thm_OAI_CKSSphericalChart_outer_divergence
-- name    : OAI.CKSSphericalChart.outer_divergence
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:38:41.038967+00:00
-- url     : https://prove2.me/theorems/b20b336e-65a5-4475-a3f3-de02759ac4df
-- title:
--   The divergence equations linking the trace-free tensor to the outer mass
-- statement:
--   For $f_0$ smooth on $S^2$, $m\in\mathbb R$, $R>0$, and a chart point with $r>0$ and $\sin\theta\ne 0$, the components $a=$ `outerA f₀ R`, $b=$ `outerPhi f₀ R` and the mass $F=$ `outerMass f₀ m R` satisfy
--   $$\partial_\theta a+\frac{\partial_\varphi b}{\sin^2\theta}+\frac{2\cos\theta\,a}{\sin\theta}=\partial_\theta F,\qquad \partial_\theta b-\partial_\varphi a+\frac{\cos\theta\, b}{\sin\theta}=\partial_\varphi F.$$
--   These say that the sphere tensor with components $a,b$ has divergence equal to the angular gradient of the mass. It is the tensor that cancels the gradient term in the momentum constraint.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem outer_divergence (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
--       {R : ℝ} (hR : 0 < R) {x : Point} (hr : 0 < x 0) (hs : Real.sin (x 1) ≠ 0) :
--       (D (basis 1) (outerA f₀ R) x + D (basis 2) (outerPhi f₀ R) x / Real.sin (x 1)^2 +
--         2*Real.cos (x 1)*outerA f₀ R x / Real.sin (x 1) = D (basis 1) (outerMass f₀ m R) x) ∧
--       (D (basis 1) (outerPhi f₀ R) x - D (basis 2) (outerA f₀ R) x +
--         Real.cos (x 1)*outerPhi f₀ R x / Real.sin (x 1) = D (basis 2) (outerMass f₀ m R) x)
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/HeatRadial.lean`, lines 93-99, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/HeatRadial.lean#L93-L99 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

theorem outer_divergence (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : Point} (hr : 0 < x 0) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (outerA f₀ R) x + D (basis 2) (outerPhi f₀ R) x / Real.sin (x 1)^2 +
      2*Real.cos (x 1)*outerA f₀ R x / Real.sin (x 1) = D (basis 1) (outerMass f₀ m R) x) ∧
    (D (basis 1) (outerPhi f₀ R) x - D (basis 2) (outerA f₀ R) x +
      Real.cos (x 1)*outerPhi f₀ R x / Real.sin (x 1) = D (basis 2) (outerMass f₀ m R) x) := by
  sorry

end
end CKSSphericalChart
end
end OAI
