-- Prove2me | Theorems.Thm_OAI_CubicTorus_TrueRadialTube_exists_revolution_CMC
-- name    : OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:26:11.685969+00:00
-- url     : https://prove2.me/theorems/6aaea9e4-8896-4613-b44e-47bd37662cd2
-- title:
--   OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC` of [lean/OAI/Geometry/CubicTorus/Reflection/RevolutionTangents.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/RevolutionTangents.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem TrueRadialTube.exists_revolution_CMC {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       {c : Cover} {r : ℝ × ℝ → ℝ} (htube : TrueRadialTube E c r)
--       (hangle : ∀ t a,r (t,a)=r (t,0)) :
--       let R := fun t => r (t,0)
--       ∃ (μ : FiniteMeasure NormalBundle) (H σ : ℝ) (N : Cover → Cover)
--         (hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hp : ∀ m x,N (x+latticeVector m)=N x),
--         IsNormalMeasure E μ ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--           (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
--         (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
--           0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
--         σ^2=1 ∧
--         (∀ t,N (revolutionPoint c R t 0) 1=σ/Real.sqrt (1+(deriv R t)^2)) ∧
--         (∀ t,H/σ=1/(R t*Real.sqrt (1+(deriv R t)^2))-
--           deriv (deriv R) t/(Real.sqrt (1+(deriv R t)^2))^3) ∧
--         ∃ α : ℝ,∀ t,R t/Real.sqrt (1+(deriv R t)^2)=α+(H/σ)/2*R t^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.TrueRadialTube`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.surfaceCurvatureLp` and `OAI.CubicTorus.surfaceJacobiB` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.revolutionPoint`, `OAI.CubicTorus.surfaceH1` and `OAI.CubicTorus.surfaceMean` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_first_transition_standard` and `OAI.CubicTorus.isMinimizerAt_no_monotone_revolution` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/RevolutionTangents.lean (declaration OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC)

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

theorem TrueRadialTube.exists_revolution_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (htube : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) :
    let R := fun t => r (t,0)
    ∃ (μ : FiniteMeasure NormalBundle) (H σ : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      σ^2=1 ∧
      (∀ t,N (revolutionPoint c R t 0) 1=σ/Real.sqrt (1+(deriv R t)^2)) ∧
      (∀ t,H/σ=1/(R t*Real.sqrt (1+(deriv R t)^2))-
        deriv (deriv R) t/(Real.sqrt (1+(deriv R t)^2))^3) ∧
      ∃ α : ℝ,∀ t,R t/Real.sqrt (1+(deriv R t)^2)=α+(H/σ)/2*R t^2 := by
  sorry

end CubicTorus

end
end

end OAI
end
