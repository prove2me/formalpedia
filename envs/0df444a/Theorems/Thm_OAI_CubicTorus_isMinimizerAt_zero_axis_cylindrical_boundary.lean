-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_zero_axis_cylindrical_boundary
-- name    : OAI.CubicTorus.isMinimizerAt_zero_axis_cylindrical_boundary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:14:58.209934+00:00
-- url     : https://prove2.me/theorems/4f8bb958-bef8-41e2-bc07-7c9f1de5cb3d
-- title:
--   OAI.CubicTorus.isMinimizerAt_zero_axis_cylindrical_boundary: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_zero_axis_cylindrical_boundary` of [lean/OAI/Geometry/CubicTorus/Profiles/TransverseTorus.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/TransverseTorus.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_zero_axis_cylindrical_boundary {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hc : IsPreconnected (frontier (openRepresentative E)))
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--         (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
--       (i : Fin 3)
--       (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → N x i=0) :
--       0 < |H⁻¹| ∧ |H⁻¹| < 1/2 ∧ ∃ c : Cover,
--         sibling_axialProjection (EuclideanSpace.single i 1) c=c ∧
--         frontier (openRepresentative E)=quotientMap '' axialCylinder (EuclideanSpace.single i 1) c |H⁻¹|
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.axialCylinder`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.sibling_axialProjection` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant` and `OAI_CubicTorus_isMinimizerAt_nonstandard_strict_signs_of_actual_normal` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/TransverseTorus.lean (declaration OAI.CubicTorus.isMinimizerAt_zero_axis_cylindrical_boundary)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

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

theorem isMinimizerAt_zero_axis_cylindrical_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (i : Fin 3)
    (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → N x i=0) :
    0 < |H⁻¹| ∧ |H⁻¹| < 1/2 ∧ ∃ c : Cover,
      sibling_axialProjection (EuclideanSpace.single i 1) c=c ∧
      frontier (openRepresentative E)=quotientMap '' axialCylinder (EuclideanSpace.single i 1) c |H⁻¹| := by
  sorry

end CubicTorus

end
end

end

end OAI
end
