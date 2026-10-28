-- Prove2me | Theorems.Thm_OAI_Kadison_SchurWeyl_matrix_union_expansion
-- name    : OAI.Kadison.SchurWeyl.matrix_union_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:49:47.66699+00:00
-- url     : https://prove2.me/theorems/8cc2aae2-2b28-4560-83df-a399e026f2be
-- title:
--   OAI.Kadison.SchurWeyl.matrix_union_expansion: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.SchurWeyl`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem matrix_union_expansion (I : ℕ → Type*)
--       [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
--       (φ : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →ₐ[ℂ] Matrix (I m) (I m) ℂ)
--       (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
--       (F : ∀ n, MultilinearMap ℂ (fun _ : J => Matrix (I n) (I n) ℂ) ℂ)
--       (hinv : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)) (A : J → Matrix (I n) (I n) ℂ),
--         F n (fun j => (u : Matrix (I n) (I n) ℂ) * A j * star (u : Matrix (I n) (I n) ℂ)) = F n A)
--       (hcomp : ∀ n m (h : n ≤ m) (A : J → Matrix (I n) (I n) ℂ),
--         F m (fun j => φ h (A j)) = F n A) :
--       ∃ c : Equiv.Perm J → ℂ, ∀ n (A : J → Matrix (I n) (I n) ℂ),
--         F n A = ∑ σ, c σ * cycleTrace σ A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.SchurWeyl.cycleTrace` (definitions bundle `OAIQ039C029` of this split).
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

namespace Kadison.SchurWeyl

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem matrix_union_expansion (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (F : ∀ n, MultilinearMap ℂ (fun _ : J => Matrix (I n) (I n) ℂ) ℂ)
    (hinv : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)) (A : J → Matrix (I n) (I n) ℂ),
      F n (fun j => (u : Matrix (I n) (I n) ℂ) * A j * star (u : Matrix (I n) (I n) ℂ)) = F n A)
    (hcomp : ∀ n m (h : n ≤ m) (A : J → Matrix (I n) (I n) ℂ),
      F m (fun j => φ h (A j)) = F n A) :
    ∃ c : Equiv.Perm J → ℂ, ∀ n (A : J → Matrix (I n) (I n) ℂ),
      F n A = ∑ σ, c σ * cycleTrace σ A := by
  sorry

end Kadison.SchurWeyl
end

end OAI
end
