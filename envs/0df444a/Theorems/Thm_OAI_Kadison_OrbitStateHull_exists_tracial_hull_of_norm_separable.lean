-- Prove2me | Theorems.Thm_OAI_Kadison_OrbitStateHull_exists_tracial_hull_of_norm_separable
-- name    : OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:57:27.775518+00:00
-- url     : https://prove2.me/theorems/667d344f-8586-49e0-8c72-b39b3db84239
-- title:
--   OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OrbitStateHull`, with `open scoped InnerProductSpace ComplexOrder Topology`):
--
--   ```lean
--   theorem exists_tracial_hull_of_norm_separable (x : H)
--       (hsep : TopologicalSpace.IsSeparable (WeakDual.toStrongDual '' hull M x)) :
--       ∃ f : WeakDual ℂ M, f∈hull M x ∧ ∀ a b : M,f (a*b)=f (b*a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.OrbitStateHull.hull` (definitions bundle `OAIQ039C039` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.uniform_commutator_separable_factor` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C039

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

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.OrbitStateHull

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

theorem exists_tracial_hull_of_norm_separable (x : H)
    (hsep : TopologicalSpace.IsSeparable (WeakDual.toStrongDual '' hull M x)) :
    ∃ f : WeakDual ℂ M, f∈hull M x ∧ ∀ a b : M,f (a*b)=f (b*a) := by
  sorry

end Kadison.OrbitStateHull

end

end
end

end OAI
end
