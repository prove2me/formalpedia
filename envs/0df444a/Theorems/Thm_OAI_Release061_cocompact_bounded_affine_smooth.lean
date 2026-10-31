-- Prove2me | Theorems.Thm_OAI_Release061_cocompact_bounded_affine_smooth
-- name    : OAI.Release061.cocompact_bounded_affine_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:43:52.524904+00:00
-- url     : https://prove2.me/theorems/7ff5a809-f07a-4792-9440-b4758fd6bd57
-- title:
--   OAI.Release061.cocompact_bounded_affine_smooth: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.cocompact_bounded_affine_smooth` of [lean/OAI/Analysis/SymmetricDomains/DiscRelationCompactLocal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/DiscRelationCompactLocal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Filter Topology`, `open Set Filter Metric MeasureTheory`, `open scoped Topology`, `open Polynomial`, `open Polynomial Algebra`, `open scoped nonZeroDivisors`, `open Polynomial Algebra`):
--
--   ```lean
--   theorem cocompact_bounded_affine_smooth {n : ℕ} (V U : Set (Affine n))
--       (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
--       (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
--       (hconn : IsConnected U) (hbounded : Bornology.IsBounded U)
--       (Γ : Type*) [Group Γ] [MulAction Γ U]
--       [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
--       (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
--       IsSmooth U
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.Affine`, `OAI.Release061.HolomorphicOnSubset`, `OAI.Release061.IsAffineAlgebraic` and `OAI.Release061.IsSmooth` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proofs of `OAI.Release061.original_small_slope_good_supported_boundary` and `OAI.Release061.original_supported_hermitian_model` of this split import it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/DiscRelationCompactLocal.lean (declaration OAI.Release061.cocompact_bounded_affine_smooth)

import Mathlib
import Definitions.Def_SymmetricDomains

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem cocompact_bounded_affine_smooth {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hconn : IsConnected U) (hbounded : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    IsSmooth U := by
  sorry

end Release061

end OAI
end
