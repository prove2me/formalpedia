-- Prove2me | Theorems.Thm_OAI_Kadison_RepresentedTower_exists_tower_average
-- name    : OAI.Kadison.RepresentedTower.exists_tower_average
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:39.564303+00:00
-- url     : https://prove2.me/theorems/99031701-2f04-4423-ba5f-75f2ea28190f
-- title:
--   OAI.Kadison.RepresentedTower.exists_tower_average: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.RepresentedTower`, with `open scoped Matrix.Norms.L2Operator Topology`, `open MeasureTheory Filter`):
--
--   ```lean
--   theorem exists_tower_average (hφ : Monotone (fun n => (φ n).range))
--       (Y : K →L[ℂ] K) {δ : ℝ} (hδ : 0≤δ)
--       (hb : ∀ u : unitary A,‖Y*ρ (u:A)-ρ (u:A)*Y‖≤δ) :
--       ∃ Z : K →L[ℂ] K,‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
--         ∀ a : K →L[ℂ] K,a∈Set.centralizer (Set.centralizer
--           ((iSup fun n => (ρ.comp (φ n)).range : StarSubalgebra ℂ (K →L[ℂ] K)) : Set (K →L[ℂ] K))) → Z*a=a*Z
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.original_copies_average` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator Topology

open MeasureTheory Filter

namespace Kadison.RepresentedTower

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]

variable (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

theorem exists_tower_average (hφ : Monotone (fun n => (φ n).range))
    (Y : K →L[ℂ] K) {δ : ℝ} (hδ : 0≤δ)
    (hb : ∀ u : unitary A,‖Y*ρ (u:A)-ρ (u:A)*Y‖≤δ) :
    ∃ Z : K →L[ℂ] K,‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      ∀ a : K →L[ℂ] K,a∈Set.centralizer (Set.centralizer
        ((iSup fun n => (ρ.comp (φ n)).range : StarSubalgebra ℂ (K →L[ℂ] K)) : Set (K →L[ℂ] K))) → Z*a=a*Z := by
  sorry

end Kadison.RepresentedTower

end

end
end

end OAI
end
