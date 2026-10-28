-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_mean_square_equality_spherical
-- name    : OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:05:00.047157+00:00
-- url     : https://prove2.me/theorems/2d50aebe-b242-4f65-a8cc-d994704e830b
-- title:
--   OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical` of [lean/OAI/Geometry/CubicTorus/Rigidity/LocalGraphSphere.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Rigidity/LocalGraphSphere.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_mean_square_equality_spherical {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hc : IsPreconnected (frontier (openRepresentative E)))
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
--         (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1))
--       {H : ℝ} (hH : H≠0)
--       (hd : ∀ᵐ z ∂(μ : Measure NormalBundle),divergence N z.1=H)
--       (heq : (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
--         ∂(μ : Measure NormalBundle))=H^2*isoperimetricProfile V) :
--       0 < |2/H| ∧ |2/H|<1/2 ∧ ∃ c : Cover,
--         frontier (openRepresentative E)=quotientMap '' Metric.sphere c |2/H|
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.coverTrace`, `OAI.CubicTorus.isoperimetricProfile` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical` and `OAI.CubicTorus.isMinimizerAt_positive_position_spherical` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Rigidity/LocalGraphSphere.lean (declaration OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_mean_square_equality_spherical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1))
    {H : ℝ} (hH : H≠0)
    (hd : ∀ᵐ z ∂(μ : Measure NormalBundle),divergence N z.1=H)
    (heq : (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle))=H^2*isoperimetricProfile V) :
    0 < |2/H| ∧ |2/H|<1/2 ∧ ∃ c : Cover,
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c |2/H| := by
  sorry

end CubicTorus

end
end

end

end OAI
end
