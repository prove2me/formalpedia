-- Prove2me | Theorems.Thm_OAI_Kadison_SchurWeyl_cycleTrace_map
-- name    : OAI.Kadison.SchurWeyl.cycleTrace_map
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:48:58.933984+00:00
-- url     : https://prove2.me/theorems/2fa44bac-3980-4d01-88c2-fb6402764979
-- title:
--   OAI.Kadison.SchurWeyl.cycleTrace_map: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.SchurWeyl`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem cycleTrace_map (φ : Matrix I I ℂ →ₐ[ℂ] Matrix K K ℂ)
--       (σ : Equiv.Perm J) (A : J → Matrix I I ℂ) :
--       cycleTrace σ (fun j => φ (A j)) = cycleTrace σ A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.SchurWeyl.cycleTrace` (definitions bundle `OAIQ039C029` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.SchurWeyl.matrix_union_expansion` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C029

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {I K J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype K] [DecidableEq K] [Nonempty K] [Fintype J] [DecidableEq J]

theorem cycleTrace_map (φ : Matrix I I ℂ →ₐ[ℂ] Matrix K K ℂ)
    (σ : Equiv.Perm J) (A : J → Matrix I I ℂ) :
    cycleTrace σ (fun j => φ (A j)) = cycleTrace σ A := by
  sorry

end Kadison.SchurWeyl
end

end OAI
end
