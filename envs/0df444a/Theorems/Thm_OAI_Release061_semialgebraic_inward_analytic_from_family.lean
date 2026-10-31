-- Prove2me | Theorems.Thm_OAI_Release061_semialgebraic_inward_analytic_from_family
-- name    : OAI.Release061.semialgebraic_inward_analytic_from_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:52:15.603839+00:00
-- url     : https://prove2.me/theorems/a90fa874-2a55-439f-ac9b-0813f813df95
-- title:
--   OAI.Release061.semialgebraic_inward_analytic_from_family: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.semialgebraic_inward_analytic_from_family` of [lean/OAI/Analysis/SymmetricDomains/SemialgebraicOffsetLimitsFamily.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SemialgebraicOffsetLimitsFamily.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology Metric MeasureTheory Classical`, `open SignElimination`):
--
--   ```lean
--   theorem semialgebraic_inward_analytic_from_family {n k : ℕ}
--       (A : (Fin n → ℝ) → Set (Fin k → ℝ))
--       (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
--         {z | z.2 ∈ A z.1})
--       (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
--       (hb : ∀ s ∈ B, (s,(0 : Fin k → ℝ)) ∈
--         closure {p : (Fin n → ℝ) × (Fin k → ℝ) | p.2 ∈ A p.1}) :
--       ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
--         ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ η > 0,
--           ∃ ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ),
--             ball s r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 η) ∧
--             (∀ x ∈ ball s r, ψ (x,0) = 0) ∧
--             ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η, ψ (x,t) ∈ A x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.PolynomialSignSet` (definitions bundle `OAIQ025S001` of this split).
--
--   **Used by.** The proof of `OAI.Release061.NashBoundaryChart.locally_small_slope_good` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SemialgebraicOffsetLimitsFamily.lean (declaration OAI.Release061.semialgebraic_inward_analytic_from_family)

import Mathlib
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
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

theorem semialgebraic_inward_analytic_from_family {n k : ℕ}
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A z.1})
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (hb : ∀ s ∈ B, (s,(0 : Fin k → ℝ)) ∈
      closure {p : (Fin n → ℝ) × (Fin k → ℝ) | p.2 ∈ A p.1}) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ η > 0,
        ∃ ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ),
          ball s r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 η) ∧
          (∀ x ∈ ball s r, ψ (x,0) = 0) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η, ψ (x,t) ∈ A x := by
  sorry

end Release061

end

end OAI
end
