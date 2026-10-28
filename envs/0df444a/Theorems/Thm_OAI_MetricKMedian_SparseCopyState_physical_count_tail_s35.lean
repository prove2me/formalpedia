-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseCopyState_physical_count_tail_s35
-- name    : OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:42:29.896141+00:00
-- url     : https://prove2.me/theorems/f312bbad-fdd9-4006-8059-0a7e7689e002
-- title:
--   OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseCopyState`, with `open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic CopyState`):
--
--   ```lean
--   theorem physical_count_tail_s35 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
--       {g p : ℚ} {φ b : ℝ} (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
--       (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hG : ∀ i, (G i).card=Δ) (hpp : 0 ≤ p ∧ p ≤ 1)
--       (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ φ*(g:ℝ)) :
--       let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
--       let H := univ.filter (fun h => max 1 (b*amount m) < m h)
--       let D := heavyActions (graphActions G) H
--       ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
--         (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
--       (∀ e, (q e:ℝ)=bias m (p:ℝ) φ (heavyParent (graphActions G) H e)) →
--       (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ) p q hpp hq).real.prob
--         (fun Z => mass (g:ℝ) A+4/((g:ℝ)*b) < mass (g:ℝ) (next Δ A (roundErased A G H Z) (roundOpened A G H Z))) ≤
--           96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FiniteLaw.prob`, `OAI.MetricKMedian.FixedBatch.Actions`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.heavyParent`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SourceBalance.amount` and `OAI.MetricKMedian.SourceBalance.bias` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.CopyState.next` and `OAI.MetricKMedian.CopyState.roundErased` (definitions bundle `OAIQ035K015` of this split); `OAI.MetricKMedian.CopyState.roundOpened` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FixedBatch.balancedActions` and `OAI.MetricKMedian.FixedBatch.balancedConflicts` (definitions bundle `OAIQ035K021` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalBatchData.proposal_count_tail_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCopyState
open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic CopyState
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem physical_count_tail_s35 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    {g p : ℚ} {φ b : ℝ} (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hG : ∀ i, (G i).card=Δ) (hpp : 0 ≤ p ∧ p ≤ 1)
    (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ φ*(g:ℝ)) :
    let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
      (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
    (∀ e, (q e:ℝ)=bias m (p:ℝ) φ (heavyParent (graphActions G) H e)) →
    (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ) p q hpp hq).real.prob
      (fun Z => mass (g:ℝ) A+4/((g:ℝ)*b) < mass (g:ℝ) (next Δ A (roundErased A G H Z) (roundOpened A G H Z))) ≤
        96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ)) := by
  sorry

end MetricKMedian.SparseCopyState
end
end

end OAI
end
