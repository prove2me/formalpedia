-- Prove2me | Theorems.Thm_OAI_Kadison_SchurWeyl_endpoint_coefficients_vanish_of_rank_one
-- name    : OAI.Kadison.SchurWeyl.endpoint_coefficients_vanish_of_rank_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:48:41.341673+00:00
-- url     : https://prove2.me/theorems/7c28ec40-512c-402d-9c26-747aa7b01c69
-- title:
--   OAI.Kadison.SchurWeyl.endpoint_coefficients_vanish_of_rank_one: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.SchurWeyl`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`):
--
--   ```lean
--   theorem endpoint_coefficients_vanish_of_rank_one
--       (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
--       (a : J) (b : ∀ n, J → I n) (hb : ∀ n, Function.Injective (b n))
--       (F : ∀ n, (J → Matrix (I n) (I n) ℂ) → ℂ)
--       (c : Equiv.Perm J → ℂ) (C : ℝ) (hC : 0 ≤ C)
--       (hF : ∀ n A, F n A = ∑ σ, c σ * cycleTrace σ A)
--       (hbound : ∀ n (σ : Equiv.Perm J), ‖F n (fun j => Matrix.single (b n (σ j)) (b n j) 1)‖ ≤
--         C * (Fintype.card (I n) : ℝ)⁻¹ *
--           (Real.sqrt (Fintype.card (I n) : ℝ)⁻¹) ^ (Fintype.card J - 1))
--       (hunbounded : ∀ B : ℕ, ∃ n, B ≤ Fintype.card (I n))
--       (σ : Equiv.Perm J) (hσ : 2 * cycleCount σ < Fintype.card J + 1) : c σ = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.SchurWeyl.cycleCount` and `OAI.Kadison.SchurWeyl.cycleTrace` (definitions bundle `OAIQ039C029` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff` of this split imports it.
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
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.SchurWeyl

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem endpoint_coefficients_vanish_of_rank_one
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    (a : J) (b : ∀ n, J → I n) (hb : ∀ n, Function.Injective (b n))
    (F : ∀ n, (J → Matrix (I n) (I n) ℂ) → ℂ)
    (c : Equiv.Perm J → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n A, F n A = ∑ σ, c σ * cycleTrace σ A)
    (hbound : ∀ n (σ : Equiv.Perm J), ‖F n (fun j => Matrix.single (b n (σ j)) (b n j) 1)‖ ≤
      C * (Fintype.card (I n) : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card (I n) : ℝ)⁻¹) ^ (Fintype.card J - 1))
    (hunbounded : ∀ B : ℕ, ∃ n, B ≤ Fintype.card (I n))
    (σ : Equiv.Perm J) (hσ : 2 * cycleCount σ < Fintype.card J + 1) : c σ = 0 := by
  sorry

end Kadison.SchurWeyl
end

end OAI
end
