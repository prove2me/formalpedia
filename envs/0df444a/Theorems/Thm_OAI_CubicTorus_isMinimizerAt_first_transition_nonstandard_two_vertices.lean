-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_first_transition_nonstandard_two_vertices
-- name    : OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:04:32.569878+00:00
-- url     : https://prove2.me/theorems/df14ded9-fe70-4500-be0b-be87cc75a374
-- title:
--   OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices` of [lean/OAI/Geometry/CubicTorus/Profiles/MinimizerFirstTransitionTube.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/MinimizerFirstTransitionTube.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_first_transition_nonstandard_two_vertices
--       {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
--       (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
--       ∃ (v : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
--         (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x)
--         (c : Fin 3 → Bool) (H : ℝ) (i : Fin 3),
--         MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+v) ⁻¹' E) ∧ IsMinimizerAt (4*Real.pi/81) F ∧
--         IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         (∀ j : Fin 3,coordinateReflection j ⁻¹' F =ᵐ[torusVolume] F) ∧
--         (∀ (x : Cover) (j : Fin 3),
--           quotientMap x∈frontier (openRepresentative F)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j) ∧
--         (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
--           H*directionalFlux F D.coordinate D.function) ∧
--         (∀ j : Fin 3,axialFluxWeight μ j<1) ∧
--         (∀ b : Fin 3 → Bool,quotientMap (chamberVertex c b)∈openRepresentative F ↔
--           b=(fun _ => false) ∨ b=(fun j => decide (j=i)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.axialFluxWeight`, `OAI.CubicTorus.chamberVertex`, `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.Periodic.Variation` and `OAI.CubicTorus.Periodic.normalFirstVariation` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.SmallStandardRegion`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.first_transition_nonstandard_monotone_revolution` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/MinimizerFirstTransitionTube.lean (declaration OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_first_transition_nonstandard_two_vertices
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (v : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x)
      (c : Fin 3 → Bool) (H : ℝ) (i : Fin 3),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+v) ⁻¹' E) ∧ IsMinimizerAt (4*Real.pi/81) F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ j : Fin 3,coordinateReflection j ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ (x : Cover) (j : Fin 3),
        quotientMap x∈frontier (openRepresentative F)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j) ∧
      (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
        H*directionalFlux F D.coordinate D.function) ∧
      (∀ j : Fin 3,axialFluxWeight μ j<1) ∧
      (∀ b : Fin 3 → Bool,quotientMap (chamberVertex c b)∈openRepresentative F ↔
        b=(fun _ => false) ∨ b=(fun j => decide (j=i))) := by
  sorry

end CubicTorus

end
end

end OAI
end
