-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_nodal_splice_closed
-- name    : OAI.CubicTorus.isMinimizerAt_nodal_splice_closed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:33:21.879802+00:00
-- url     : https://prove2.me/theorems/37e52a6f-abc8-41b7-b426-4dedb324da71
-- title:
--   OAI.CubicTorus.isMinimizerAt_nodal_splice_closed: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_nodal_splice_closed` of [lean/OAI/Geometry/CubicTorus/Estimates/NodalBalanceValue.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/NodalBalanceValue.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_nodal_splice_closed {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--         ∀ᶠ y in 𝓝 x,‖N y‖=1)
--       {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
--       (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
--       {F : Torus → ℝ} (hFm : Measurable F)
--       (hF : ContinuousOn F (frontier (openRepresentative E)))
--       (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
--       (v : Cover) {D : Set Torus}
--       (hD : IsPositiveNodalPiece (directionalNormalScalar N hN hp v)
--         (frontier (openRepresentative E)) D)
--       {k : ℝ} (hk : k≠0)
--       (hFD : ∀ a∈D,F a=k*⟪v,N (representative a)⟫)
--       (hFzero : ∀ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫≤0 → F a=0) :
--       IsClosed D
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.IsPositiveNodalPiece`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.directionalNormalScalar`, `OAI.CubicTorus.normalProjection`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.representative`, `OAI.CubicTorus.surfaceCurvatureLp` and `OAI.CubicTorus.surfaceJacobiB` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.surfaceH1` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.Periodic.isMinimizerAt_translation_nodal_count` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/NodalBalanceValue.lean (declaration OAI.CubicTorus.isMinimizerAt_nodal_splice_closed)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

theorem isMinimizerAt_nodal_splice_closed {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (v : Cover) {D : Set Torus}
    (hD : IsPositiveNodalPiece (directionalNormalScalar N hN hp v)
      (frontier (openRepresentative E)) D)
    {k : ℝ} (hk : k≠0)
    (hFD : ∀ a∈D,F a=k*⟪v,N (representative a)⟫)
    (hFzero : ∀ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫≤0 → F a=0) :
    IsClosed D := by
  sorry

end CubicTorus

end
end

end OAI
end
