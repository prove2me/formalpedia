-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_corner_arbitrarily_large_alphabet
-- name    : OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:38:16.645647+00:00
-- url     : https://prove2.me/theorems/d97166cd-cfdf-4713-bfd4-915610796f8b
-- title:
--   OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped BigOperators ComplexOrder InnerProductSpace`, `open Filter Topology`, `open scoped Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma corner_arbitrarily_large_alphabet (n : ℕ) (p : Matrix (I n) (I n) ℂ)
--       (hp : IsStarProjection p) (α : ℝ) (hα : 0<α) (hατ : τ (φ n p)=(α:ℂ)) (N : ℕ) :
--       ∃ m : ℕ, N ≤ m ∧ ∃ x : Fin m → A,
--         Orthonormal ℂ (fun i => algebraVector τ (x i)) ∧
--         ∀ i, τ (x i)=0 ∧ x i*φ n p=x i ∧ star (x i)*x i=((α:ℂ)⁻¹) • φ n p ∧
--           ‖x i‖≤(Real.sqrt α)⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.algebraVector` (definitions bundle `OAIQ039C003` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.exists_corner_weak_zero` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C003

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

open Filter Topology

open scoped Matrix.Norms.L2Operator

namespace Kadison.TracialGNS

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ)
  (hτ : ∀ a b, τ (a*b)=τ (b*a))
  (h1 : τ 1=1)
  (I : ℕ → Type*)
  [∀ n, Fintype (I n)]
  [∀ n, DecidableEq (I n)]
  [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
  (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

include hτ h1 e he hsize in
lemma corner_arbitrarily_large_alphabet (n : ℕ) (p : Matrix (I n) (I n) ℂ)
    (hp : IsStarProjection p) (α : ℝ) (hα : 0<α) (hατ : τ (φ n p)=(α:ℂ)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∃ x : Fin m → A,
      Orthonormal ℂ (fun i => algebraVector τ (x i)) ∧
      ∀ i, τ (x i)=0 ∧ x i*φ n p=x i ∧ star (x i)*x i=((α:ℂ)⁻¹) • φ n p ∧
        ‖x i‖≤(Real.sqrt α)⁻¹ := by
  sorry

end Kadison.TracialGNS

end

end
end

end OAI
end
