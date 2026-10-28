-- Prove2me | Theorems.Thm_OAI_Kadison_SchurWeyl_centered_expansion_pairings
-- name    : OAI.Kadison.SchurWeyl.centered_expansion_pairings
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:49:10.637995+00:00
-- url     : https://prove2.me/theorems/6a4a9b10-8eb0-4601-b3b6-f64f7ca96a60
-- title:
--   OAI.Kadison.SchurWeyl.centered_expansion_pairings: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.SchurWeyl`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem centered_expansion_pairings (a : J) (d : Equiv.Perm J → ℂ)
--       (hd : ∀ σ, 2 * cycleCount σ < Fintype.card J + 1 → d σ = 0)
--       (A : J → Matrix I I ℂ) (hA : ∀ j, j ≠ a → Matrix.trace (A j) = 0) :
--       (∑ σ, d σ * cycleTrace σ A) =
--         ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm J =>
--           σ a = a ∧ (∀ j, σ (σ j) = j) ∧ ∀ j, σ j = j → j = a),
--         d σ * cycleTrace σ A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.SchurWeyl.cycleCount` and `OAI.Kadison.SchurWeyl.cycleTrace` (definitions bundle `OAIQ039C029` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.SchurWeyl.centered_expansion_contractions` of this split imports it.
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

variable {𝕜 I J : Type*} [CommRing 𝕜] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

theorem centered_expansion_pairings (a : J) (d : Equiv.Perm J → ℂ)
    (hd : ∀ σ, 2 * cycleCount σ < Fintype.card J + 1 → d σ = 0)
    (A : J → Matrix I I ℂ) (hA : ∀ j, j ≠ a → Matrix.trace (A j) = 0) :
    (∑ σ, d σ * cycleTrace σ A) =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm J =>
        σ a = a ∧ (∀ j, σ (σ j) = j) ∧ ∀ j, σ j = j → j = a),
      d σ * cycleTrace σ A := by
  sorry

end Kadison.SchurWeyl
end

end OAI
end
