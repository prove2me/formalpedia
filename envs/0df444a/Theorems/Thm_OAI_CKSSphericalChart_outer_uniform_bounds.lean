-- Prove2me | Theorems.Thm_OAI_CKSSphericalChart_outer_uniform_bounds
-- name    : OAI.CKSSphericalChart.outer_uniform_bounds
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:38:51.986415+00:00
-- url     : https://prove2.me/theorems/620a867b-a1bc-4a3e-bca5-c18c7895d8e5
-- title:
--   Uniform bounds for the outer mass and its tensor
-- statement:
--   For $f_0$ smooth on $S^2$ and $m\in\mathbb R$ there are constants $M,B,T\ge 0$, independent of $R$, such that for all $R\ge 12$ and chart points with $r\ge 3R$ and $\sin\theta\ne 0$,
--   $$|F|\le M,\quad |\Delta_{S^2}F|\le B,\quad |\nabla_{S^2}F|\le B,\quad a^2+(b/\sin\theta)^2\le T^2,$$
--   where $F=$ `outerMass f₀ m R`, $a=$ `outerA f₀ R`, $b=$ `outerPhi f₀ R`.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem outer_uniform_bounds (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
--       ∃ M B T : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ 0 ≤ T ∧
--       ∀ R : ℝ, 12 ≤ R → ∀ x : Point, 3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
--         |outerMass f₀ m R x| ≤ M ∧
--         |(massJet (outerMass f₀ m R) x).laplace (Real.sin (x 1)) (Real.cos (x 1))| ≤ B ∧
--         ‖sphereGrad (massJet (outerMass f₀ m R) x) (Real.sin (x 1))‖ ≤ B ∧
--         outerA f₀ R x ^ 2 + (outerPhi f₀ R x / Real.sin (x 1))^2 ≤ T^2
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/OuterBounds.lean`, lines 27-72, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/OuterBounds.lean#L27-L72 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

theorem outer_uniform_bounds (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ M B T : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ 0 ≤ T ∧
    ∀ R : ℝ, 12 ≤ R → ∀ x : Point, 3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
      |outerMass f₀ m R x| ≤ M ∧
      |(massJet (outerMass f₀ m R) x).laplace (Real.sin (x 1)) (Real.cos (x 1))| ≤ B ∧
      ‖sphereGrad (massJet (outerMass f₀ m R) x) (Real.sin (x 1))‖ ≤ B ∧
      outerA f₀ R x ^ 2 + (outerPhi f₀ R x / Real.sin (x 1))^2 ≤ T^2 := by
  sorry

end
end CKSSphericalChart
end
end OAI
