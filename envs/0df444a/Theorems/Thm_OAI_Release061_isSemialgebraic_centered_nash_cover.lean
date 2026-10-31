-- Prove2me | Theorems.Thm_OAI_Release061_isSemialgebraic_centered_nash_cover
-- name    : OAI.Release061.isSemialgebraic_centered_nash_cover
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:51:27.985988+00:00
-- url     : https://prove2.me/theorems/9b973c6b-a1c3-4527-9e20-6c07a845862d
-- title:
--   OAI.Release061.isSemialgebraic_centered_nash_cover: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.isSemialgebraic_centered_nash_cover` of [lean/OAI/Analysis/SymmetricDomains/SemialgebraicPolynomialNonzero.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SemialgebraicPolynomialNonzero.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology MeasureTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem isSemialgebraic_centered_nash_cover {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
--       ∃ C : Finset (NashPatch (n+n)), (∀ p ∈ C, 0 ∈ p.domain) ∧
--         ∀ z, z ∈ S ↔ ∃ p ∈ C, z ∈ p.complexMap '' p.domain
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.NashPatch` and `OAI.Release061.NashPatch.complexMap` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.Affine` and `OAI.Release061.IsSemialgebraic` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.prime_boundary_generic_fiber` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SemialgebraicPolynomialNonzero.lean (declaration OAI.Release061.isSemialgebraic_centered_nash_cover)

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

theorem isSemialgebraic_centered_nash_cover {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    ∃ C : Finset (NashPatch (n+n)), (∀ p ∈ C, 0 ∈ p.domain) ∧
      ∀ z, z ∈ S ↔ ∃ p ∈ C, z ∈ p.complexMap '' p.domain := by
  sorry

end

open Set
open scoped Classical

end Release061

end

end OAI
end
