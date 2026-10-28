-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_positive_position_spherical
-- name    : OAI.CubicTorus.isMinimizerAt_positive_position_spherical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:34:30.679994+00:00
-- url     : https://prove2.me/theorems/abf4ae6d-3da0-4c4a-b58e-bf50eeef4d01
-- title:
--   OAI.CubicTorus.isMinimizerAt_positive_position_spherical: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_positive_position_spherical` of [lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_positive_position_spherical {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       (hc : IsPreconnected (frontier (openRepresentative E)))
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hpN : ∀ m x,N (x+latticeVector m)=N x)
--       (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--         (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
--       (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
--         (∀ m x,F (x+latticeVector m)=F x) →
--         (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
--           H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
--       (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
--         (surfaceSmoothJet μ (normalComponentScalar N hN hpN i)) w=0)
--       {X : Cover → Cover} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
--       (hpX : ∀ m x,X (x+latticeVector m)=X x)
--       (hDX : ∀ᵐ z ∂(μ : Measure NormalBundle),fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover)
--       (hpos : ∀ᵐ z ∂(μ : Measure NormalBundle),0<⟪N z.1,X z.1⟫) :
--       ∃ (c : Cover) (r : ℝ),0 < r ∧ r<1/2 ∧
--         frontier (openRepresentative E)=quotientMap '' Metric.sphere c r
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.normalComponentScalar`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.smoothPeriodicScalars`, `OAI.CubicTorus.surfaceCurvatureLp`, `OAI.CubicTorus.surfaceJacobiB`, `OAI.CubicTorus.surfaceSmoothJet` and `OAI.CubicTorus.tangentialDivergence` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.surfaceH1` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean (declaration OAI.CubicTorus.isMinimizerAt_positive_position_spherical)

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

theorem isMinimizerAt_positive_position_spherical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hpN i)) w=0)
    {X : Cover → Cover} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hpX : ∀ m x,X (x+latticeVector m)=X x)
    (hDX : ∀ᵐ z ∂(μ : Measure NormalBundle),fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover)
    (hpos : ∀ᵐ z ∂(μ : Measure NormalBundle),0<⟪N z.1,X z.1⟫) :
    ∃ (c : Cover) (r : ℝ),0 < r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c r := by
  sorry

end CubicTorus

end
end

end OAI
end
