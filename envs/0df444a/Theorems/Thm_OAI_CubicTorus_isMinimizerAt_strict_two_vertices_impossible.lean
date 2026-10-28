-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_strict_two_vertices_impossible
-- name    : OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:13:19.719434+00:00
-- url     : https://prove2.me/theorems/3919505b-032a-491f-830d-6111adcffe09
-- title:
--   OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible` of [lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_strict_two_vertices_impossible {V : ℝ} (hVhalf : V∈Ioc 0 (1/2))
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hs : ∀ j : Fin 3,coordinateReflection j ⁻¹' E =ᵐ[torusVolume] E)
--       {c : Fin 3 → Bool}
--       (hsg : ∀ (x : Cover) (j : Fin 3),
--         quotientMap x∈frontier (openRepresentative E)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j)
--       (i : Fin 3)
--       (hv : ∀ b : Fin 3 → Bool,quotientMap (chamberVertex c b)∈openRepresentative E ↔
--         b=(fun _ => false) ∨ b=(fun j => decide (j=i))) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.chamberVertex`, `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI_CubicTorus_isMinimizerAt_cylinder_contact_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_standard` and `OAI.CubicTorus.isMinimizerAt_second_transition_nonstandard_star` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean (declaration OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible)

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

theorem isMinimizerAt_strict_two_vertices_impossible {V : ℝ} (hVhalf : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ j : Fin 3,coordinateReflection j ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (j : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j)
    (i : Fin 3)
    (hv : ∀ b : Fin 3 → Bool,quotientMap (chamberVertex c b)∈openRepresentative E ↔
      b=(fun _ => false) ∨ b=(fun j => decide (j=i))) : False := by
  sorry

end CubicTorus

end
end

end OAI
end
