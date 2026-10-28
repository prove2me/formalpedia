-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_exists_corner_weak_zero
-- name    : OAI.Kadison.TracialGNS.exists_corner_weak_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:09:22.846501+00:00
-- url     : https://prove2.me/theorems/9496cb69-ea0c-49b0-bbc8-8959c773c12e
-- title:
--   OAI.Kadison.TracialGNS.exists_corner_weak_zero: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped BigOperators ComplexOrder InnerProductSpace`, `open Filter Topology`, `open scoped Matrix.Norms.L2Operator`):
--
--   ```lean
--   theorem exists_corner_weak_zero (n : ℕ) (p : Matrix (I n) (I n) ℂ)
--       (hp : IsStarProjection p) (α : ℝ) (hα : 0<α) (hατ : τ (φ n p)=(α:ℂ)) :
--       ∃ x : ℕ → A, (∀ k, τ (x k)=0 ∧ x k*φ n p=x k ∧
--         star (x k)*x k=((α:ℂ)⁻¹) • φ n p ∧ ‖x k‖≤(Real.sqrt α)⁻¹ ∧
--         ‖τ.toPreGNS (x k)‖=1 ∧ ‖τ.toPreGNS (star (x k))‖=1) ∧
--         ∀ a : A, Tendsto (fun k => τ (x k*a)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.stageAlgebra` (definitions bundle `OAIQ039C018` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.propagation_from_stage_all` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C018

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
  (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
  (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
  (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈ Set.centralizer (Set.centralizer
    (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))))

include hτ h1 e he hsize hgen in
theorem exists_corner_weak_zero (n : ℕ) (p : Matrix (I n) (I n) ℂ)
    (hp : IsStarProjection p) (α : ℝ) (hα : 0<α) (hατ : τ (φ n p)=(α:ℂ)) :
    ∃ x : ℕ → A, (∀ k, τ (x k)=0 ∧ x k*φ n p=x k ∧
      star (x k)*x k=((α:ℂ)⁻¹) • φ n p ∧ ‖x k‖≤(Real.sqrt α)⁻¹ ∧
      ‖τ.toPreGNS (x k)‖=1 ∧ ‖τ.toPreGNS (star (x k))‖=1) ∧
      ∀ a : A, Tendsto (fun k => τ (x k*a)) atTop (𝓝 0) := by
  sorry

end Kadison.TracialGNS

end

end
end

end OAI
end
