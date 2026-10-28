-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_nodal_truncation_impossible
-- name    : OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:33:51.83991+00:00
-- url     : https://prove2.me/theorems/850fb7d5-ea2a-427c-8f4b-a540d0e3cd59
-- title:
--   OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible` of [lean/OAI/Geometry/CubicTorus/Profiles/FirstAxisShift.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FirstAxisShift.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_nodal_truncation_impossible {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
--         (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
--       (f : smoothPeriodicScalars)
--       (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
--         (surfaceSmoothJet μ f) v=0)
--       {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
--       (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u v=0)
--       {F : Torus → ℝ} (hFm : Measurable F)
--       (hF : ContinuousOn F (frontier (openRepresentative E)))
--       (haeF : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z))
--       {D : Set Torus} (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D)
--       {x : Torus} (hcl : x∈closure D) (hnot : x∉D)
--       {k : ℝ} (hk : k≠0)
--       (hFD : ∀ a∈D,F a=k*f.val (representative a))
--       (hFzero : ∀ a∈frontier (openRepresentative E),f.val (representative a)≤0 → F a=0) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.IsPositiveNodalPiece`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.directionalNormalScalar`, `OAI.CubicTorus.normalProjection`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.representative`, `OAI.CubicTorus.smoothPeriodicScalars`, `OAI.CubicTorus.surfaceCurvatureLp`, `OAI.CubicTorus.surfaceJacobiB` and `OAI.CubicTorus.surfaceSmoothJet` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.surfaceH1` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.latticeVector` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI_CubicTorus_isMinimizerAt_nonstandard_strict_signs_of_actual_normal` and `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FirstAxisShift.lean (declaration OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible)

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nodal_truncation_impossible {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u v=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (haeF : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z))
    {D : Set Torus} (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D)
    {x : Torus} (hcl : x∈closure D) (hnot : x∉D)
    {k : ℝ} (hk : k≠0)
    (hFD : ∀ a∈D,F a=k*f.val (representative a))
    (hFzero : ∀ a∈frontier (openRepresentative E),f.val (representative a)≤0 → F a=0) : False := by
  sorry

end CubicTorus

end
end

end

end OAI
end
