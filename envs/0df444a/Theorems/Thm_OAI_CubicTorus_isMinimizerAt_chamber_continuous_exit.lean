-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_chamber_continuous_exit
-- name    : OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:01:45.728346+00:00
-- url     : https://prove2.me/theorems/22db0c0d-6b92-4c4c-b349-87a61a83a43c
-- title:
--   OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit` of [lean/OAI/Geometry/CubicTorus/Estimates/CoordinatePlaneRays.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/CoordinatePlaneRays.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_chamber_continuous_exit {A : Type*} [TopologicalSpace A]
--       {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
--       {s : Fin 3 → Bool}
--       (hsg : ∀ (x : Cover) (i : Fin 3),
--         quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
--       {x y : A → Cover} (hxc : Continuous x) (hyc : Continuous y)
--       (hx : ∀ a,x a∈closedHalfBox (chamberCorner s))
--       (hy : ∀ a,y a∈closedHalfBox (chamberCorner s))
--       (hxy : ∀ a i,x a i≤y a i)
--       (hxE : ∀ a,quotientMap (x a)∈openRepresentative E)
--       (hyE : ∀ a,quotientMap (y a)∉closure (openRepresentative E)) :
--       ∃ r : A → ℝ,Continuous r ∧ (∀ a,r a∈Ioo (0 : ℝ) 1) ∧
--         (∀ a,quotientMap (chamberSegment (x a) (y a) (r a))∈frontier (openRepresentative E)) ∧
--         (∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈openRepresentative E ↔ t < r a)) ∧
--         (∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈closure (openRepresentative E) ↔ t ≤ r a)) ∧
--         ∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈frontier (openRepresentative E) ↔ t=r a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.chamberCorner`, `OAI.CubicTorus.chamberSegment`, `OAI.CubicTorus.closedHalfBox`, `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_smooth_radial_section_of_level_vertices` and `OAI.CubicTorus.isMinimizerAt_tubular_sections` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/CoordinatePlaneRays.lean (declaration OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_chamber_continuous_exit {A : Type*} [TopologicalSpace A]
    {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {x y : A → Cover} (hxc : Continuous x) (hyc : Continuous y)
    (hx : ∀ a,x a∈closedHalfBox (chamberCorner s))
    (hy : ∀ a,y a∈closedHalfBox (chamberCorner s))
    (hxy : ∀ a i,x a i≤y a i)
    (hxE : ∀ a,quotientMap (x a)∈openRepresentative E)
    (hyE : ∀ a,quotientMap (y a)∉closure (openRepresentative E)) :
    ∃ r : A → ℝ,Continuous r ∧ (∀ a,r a∈Ioo (0 : ℝ) 1) ∧
      (∀ a,quotientMap (chamberSegment (x a) (y a) (r a))∈frontier (openRepresentative E)) ∧
      (∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈openRepresentative E ↔ t < r a)) ∧
      (∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈closure (openRepresentative E) ↔ t ≤ r a)) ∧
      ∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈frontier (openRepresentative E) ↔ t=r a) := by
  sorry

end CubicTorus

end
end

end OAI
end
