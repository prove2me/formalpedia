-- Prove2me | Theorems.Thm_OAI_Release061_NashPatch_principal_rank_dichotomy
-- name    : OAI.Release061.NashPatch.principal_rank_dichotomy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:49:21.7639+00:00
-- url     : https://prove2.me/theorems/d7c16c97-ef29-4b2d-8305-b75caeb95b52
-- title:
--   OAI.Release061.NashPatch.principal_rank_dichotomy: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.NashPatch.principal_rank_dichotomy` of [lean/OAI/Analysis/SymmetricDomains/SemialgebraicPolynomialNonzero.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SemialgebraicPolynomialNonzero.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061.NashPatch`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology MeasureTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem principal_rank_dichotomy {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
--       (Q : MvPolynomial (Fin n) ℂ)
--       (hcharts : ∀ q ∈ MvPolynomial.zeroLocus ℂ I, MvPolynomial.eval q Q ≠ 0 →
--         ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ I ∧
--           IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' W) ∧ q ∈ W ∧
--           ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B))
--       (p : NashPatch (n+n)) (h0 : 0 ∈ p.domain)
--       (hpI : ∀ x ∈ p.domain, p.complexMap x ∈ MvPolynomial.zeroLocus ℂ I)
--       (hpQ : ∀ x ∈ p.domain, MvPolynomial.eval (p.complexMap x) Q ≠ 0) :
--       (∃ P : MvPolynomial (Fin n) ℂ, P ∉ I ∧
--         ∀ x ∈ p.domain, MvPolynomial.eval (p.complexMap x) P = 0) ∨
--         volume {x | x ∈ p.domain ∧ p.complexRank x < m} = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.NashPatch`, `OAI.Release061.NashPatch.complexMap` and `OAI.Release061.NashPatch.complexRank` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.Affine` and `OAI.Release061.Biholomorph` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.prime_boundary_generic_fiber` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SemialgebraicPolynomialNonzero.lean (declaration OAI.Release061.NashPatch.principal_rank_dichotomy)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology MeasureTheory
open scoped Classical

namespace NashPatch

theorem principal_rank_dichotomy {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (Q : MvPolynomial (Fin n) ℂ)
    (hcharts : ∀ q ∈ MvPolynomial.zeroLocus ℂ I, MvPolynomial.eval q Q ≠ 0 →
      ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ I ∧
        IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' W) ∧ q ∈ W ∧
        ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B))
    (p : NashPatch (n+n)) (h0 : 0 ∈ p.domain)
    (hpI : ∀ x ∈ p.domain, p.complexMap x ∈ MvPolynomial.zeroLocus ℂ I)
    (hpQ : ∀ x ∈ p.domain, MvPolynomial.eval (p.complexMap x) Q ≠ 0) :
    (∃ P : MvPolynomial (Fin n) ℂ, P ∉ I ∧
      ∀ x ∈ p.domain, MvPolynomial.eval (p.complexMap x) P = 0) ∨
      volume {x | x ∈ p.domain ∧ p.complexRank x < m} = 0 := by
  sorry

end NashPatch
end

open Set
open scoped Classical

end Release061

end

end OAI
end
