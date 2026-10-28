-- Prove2me | Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_full_jacobi_system
-- name    : OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:26:53.34221+00:00
-- url     : https://prove2.me/theorems/9011e49e-3574-4217-bfa9-28f593ab0d02
-- title:
--   OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system` of [lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.Periodic`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_full_jacobi_system {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E) :
--       ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
--         (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
--         IsNormalMeasure E μ ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--           (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
--         (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
--           (∀ m x,F (x+latticeVector m)=F x) →
--           (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
--             H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
--         (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
--           0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
--         (∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
--           (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.normalComponentScalar`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.smoothPeriodicScalars`, `OAI.CubicTorus.surfaceCurvatureLp`, `OAI.CubicTorus.surfaceJacobiB`, `OAI.CubicTorus.surfaceSmoothJet` and `OAI.CubicTorus.tangentialDivergence` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.surfaceH1` and `OAI.CubicTorus.surfaceMean` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC`, `OAI.CubicTorus.TrueRadialTube.exists_rotation_zero` and `OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean (declaration OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system)

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
namespace Periodic

theorem isMinimizerAt_full_jacobi_system {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      (∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
        (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) := by
  sorry

end Periodic
end CubicTorus

end
end

end OAI
end
