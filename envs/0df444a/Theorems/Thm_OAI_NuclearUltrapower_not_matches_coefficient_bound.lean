-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_not_matches_coefficient_bound
-- name    : OAI.NuclearUltrapower.not_matches_coefficient_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:56:24.371987+00:00
-- url     : https://prove2.me/theorems/99d5170e-7c56-4716-a199-9712c3e2ffb5
-- title:
--   OAI.NuclearUltrapower.not_matches_coefficient_bound: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.not_matches_coefficient_bound` of [lean/OAI/Analysis/NuclearUltrapower/InitialMatching.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InitialMatching.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open scoped Topology InnerProductSpace TensorProduct`):
--
--   ```lean
--   theorem not_matches_coefficient_bound (hρ : Function.Injective ρ)
--       (π : FiniteUnitaryRep.{u,v} Γ) {n : Type*} [Fintype n] [DecidableEq n]
--       (b : OrthonormalBasis n ℂ π) (a : ℝ) (ha : a ≤ 4 * (S.card : ℝ))
--       (hm : ¬ Matches ρ S u a π) :
--       ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n B) -
--         laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π.action s (b j)) i) (u s : B))‖
--         ≤ 4 * (S.card : ℝ) - a
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.FiniteUnitaryRep` and `OAI.NuclearUltrapower.coefficientMatrix` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.instPartialOrder_solutions` (definitions bundle `OAIQ019N009` of this split); `OAI.NuclearUltrapower.laplacian` (definitions bundle `OAIQ019N028` of this split); `OAI.NuclearUltrapower.instStarOrderedRing_solutions` (definitions bundle `OAIQ019N041` of this split); `OAI.NuclearUltrapower.Matches` (definitions bundle `OAIQ019N043` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.initial_match` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InitialMatching.lean (declaration OAI.NuclearUltrapower.not_matches_coefficient_bound)

import Mathlib
import Definitions.Def_OAIQ019N043

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v

section Bounds
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

attribute [local instance] OAI.NuclearUltrapower.instPartialOrder_solutions
attribute [local instance] OAI.NuclearUltrapower.instStarOrderedRing_solutions
theorem not_matches_coefficient_bound (hρ : Function.Injective ρ)
    (π : FiniteUnitaryRep.{u,v} Γ) {n : Type*} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n ℂ π) (a : ℝ) (ha : a ≤ 4 * (S.card : ℝ))
    (hm : ¬ Matches ρ S u a π) :
    ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n B) -
      laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π.action s (b j)) i) (u s : B))‖
      ≤ 4 * (S.card : ℝ) - a := by
  sorry
end Bounds
end NuclearUltrapower
end
end

end OAI
end
