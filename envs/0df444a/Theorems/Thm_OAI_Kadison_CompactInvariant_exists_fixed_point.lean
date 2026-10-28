-- Prove2me | Theorems.Thm_OAI_Kadison_CompactInvariant_exists_fixed_point
-- name    : OAI.Kadison.CompactInvariant.exists_fixed_point
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:32:41.603551+00:00
-- url     : https://prove2.me/theorems/198f426e-336b-4a22-a37c-f2f3900dd322
-- title:
--   OAI.Kadison.CompactInvariant.exists_fixed_point: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CompactInvariant`, with `open Set TopologicalSpace`):
--
--   ```lean
--   theorem exists_fixed_point (j : X ≃ₗ[ℝ] E) (hj : Continuous j.symm)
--       (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y ≤ r})
--       (hiso : ∀ g : G,∀ x y : X,dist (j (g • x)) (j (g • y))=dist (j x) (j y))
--       {C : Set X} (hcomp : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
--       (hinv : Invariant (G:=G) C) (hsep : IsSeparable (j '' C)) :
--       ∃ x∈C,∀ g : G,g • x=x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CompactInvariant.Invariant` (definitions bundle `OAIQ039C004` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C004

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Set TopologicalSpace

namespace Kadison.CompactInvariant

variable {G X E : Type*} [Group G] [TopologicalSpace X] [T2Space X]
  [AddCommGroup X] [Module ℝ X] [MulAction G X] [ContinuousConstSMul G X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixed_point (j : X ≃ₗ[ℝ] E) (hj : Continuous j.symm)
    (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y ≤ r})
    (hiso : ∀ g : G,∀ x y : X,dist (j (g • x)) (j (g • y))=dist (j x) (j y))
    {C : Set X} (hcomp : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hinv : Invariant (G:=G) C) (hsep : IsSeparable (j '' C)) :
    ∃ x∈C,∀ g : G,g • x=x := by
  sorry

end Kadison.CompactInvariant

end

end
end

end OAI
end
