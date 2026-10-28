-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_rotation_jacobi_from_germs
-- name    : OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:35:45.609204+00:00
-- url     : https://prove2.me/theorems/6a9870d9-6e1f-471d-bf24-f69dba8a6bde
-- title:
--   OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs` of [lean/OAI/Geometry/CubicTorus/Regularity/NormalRotationWeak.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/NormalRotationWeak.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_rotation_jacobi_from_germs {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--         ∀ᶠ y in 𝓝 x,‖N y‖=1) {H : ℝ}
--       (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
--         (∀ m x,F (x+latticeVector m)=F x) →
--         (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
--           H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
--       (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
--         (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0)
--       (f₁ f₂ : smoothPeriodicScalars)
--       (he : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∃ b₁ b₂ : ℝ,
--         (f₁.val =ᶠ[𝓝 x] (fun y => y 1-b₁)) ∧
--         (f₂.val =ᶠ[𝓝 x] (fun y => y 2-b₂))) :
--       ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
--         (surfaceSmoothJet μ
--           (smoothScalarMul f₁ (normalComponentScalar N hN hp 2)-
--             smoothScalarMul f₂ (normalComponentScalar N hN hp 1))) w=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.normalComponentScalar`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.smoothPeriodicScalars`, `OAI.CubicTorus.surfaceCurvatureLp`, `OAI.CubicTorus.surfaceJacobiB`, `OAI.CubicTorus.surfaceSmoothJet` and `OAI.CubicTorus.tangentialDivergence` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.smoothScalarMul` and `OAI.CubicTorus.surfaceH1` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.TrueRadialTube.exists_rotation_zero` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/NormalRotationWeak.lean (declaration OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

attribute [local irreducible] surfaceSmoothJet surfaceCurvatureLp surfaceJacobiB

theorem isMinimizerAt_rotation_jacobi_from_germs {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0)
    (f₁ f₂ : smoothPeriodicScalars)
    (he : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∃ b₁ b₂ : ℝ,
      (f₁.val =ᶠ[𝓝 x] (fun y => y 1-b₁)) ∧
      (f₂.val =ᶠ[𝓝 x] (fun y => y 2-b₂))) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ
        (smoothScalarMul f₁ (normalComponentScalar N hN hp 2)-
          smoothScalarMul f₂ (normalComponentScalar N hN hp 1))) w=0 := by
  sorry

end CubicTorus

end
end

end OAI
end
