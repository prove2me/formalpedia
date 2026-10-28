-- Prove2me | Theorems.Thm_OAI_Kadison_CompactInvariant_minimal_norm_compact
-- name    : OAI.Kadison.CompactInvariant.minimal_norm_compact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:33:01.453482+00:00
-- url     : https://prove2.me/theorems/7a576785-7a9e-4644-a7e5-493946f05af0
-- title:
--   OAI.Kadison.CompactInvariant.minimal_norm_compact: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CompactInvariant`, with `open Set TopologicalSpace`):
--
--   ```lean
--   theorem minimal_norm_compact (j : X ≃ E) (hj : Continuous j.symm)
--       (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y ≤ r})
--       (hiso : ∀ g : G,∀ x y : X,dist (j (g • x)) (j (g • y))=dist (j x) (j y))
--       {C K : Set X} (hcomp : IsCompact K)
--       (hK : Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧ Invariant (G:=G) S) K)
--       (hsep : IsSeparable (j '' K)) : IsCompact (j '' K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CompactInvariant.Invariant` (definitions bundle `OAIQ039C004` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CompactInvariant.exists_fixed_point` of this split imports it.
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
  [MulAction G X] [ContinuousConstSMul G X] [MetricSpace E] [CompleteSpace E]

theorem minimal_norm_compact (j : X ≃ E) (hj : Continuous j.symm)
    (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y ≤ r})
    (hiso : ∀ g : G,∀ x y : X,dist (j (g • x)) (j (g • y))=dist (j x) (j y))
    {C K : Set X} (hcomp : IsCompact K)
    (hK : Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧ Invariant (G:=G) S) K)
    (hsep : IsSeparable (j '' K)) : IsCompact (j '' K) := by
  sorry

end Kadison.CompactInvariant

end

end
end

end OAI
end
