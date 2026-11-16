-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_max_balance_log_ratio
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.max_balance_log_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:58:40.983204+00:00
-- url     : https://prove2.me/theorems/f7583299-2b2c-48e0-9fa5-4a23e150ed84
-- title:
--   Theorem B.2 — Max-Balance has competitive ratio Θ(log(N+1)) on the rooted line
-- statement:
--   On the rooted half-line, Max-Balance is well defined on every rooted-line input: its execution exists, is unique, and clears every request with finitely many services. Moreover its competitive ratio on inputs with $N$ requests is $\Theta(\log(N+1))$: there are constants $c>0$ and $C>0$ such that for every $N\ge1$,
--
--   1. every rooted-line input $I$ with exactly $N$ requests satisfies $\mathrm{ALG}_{\mathrm{MB}}(I)\le C\log(N+1)\,\mathrm{OPT}(I)$, and
--   2. some rooted-line input $I$ with exactly $N$ requests satisfies $\mathrm{ALG}_{\mathrm{MB}}(I)\ge c\log(N+1)\,\mathrm{OPT}(I)$.
--
--   This shows that measuring urgency by the oldest pending request in each dyadic prefix, without the offline optimum of the pending requests, loses a logarithmic factor.
--
--   Differences from the source:
--   - reading: rooted-line inputs (requests with arrival times and locations on the half-line) → locations x(r) > 0; reason: Max-Balance is undefined for a request at the root: it lies in every level and the thresholds 2^i/4 → 0, so no first tight time exists
--   - encoding: competitive ratio Θ(log(N+1)) on inputs with N requests → ∃ c C > 0, ∀ N ≥ 1: the upper bound on every input with exactly N requests and an input with exactly N requests attaining the lower bound; reason: the competitive ratio as a function of N is the supremum of ALG/OPT over those inputs; Θ fixes it between two constant multiples of log(N+1)
--   - encoding: the Max-Balance algorithm → a predicate characterising its execution, with existence, uniqueness and feasibility of the execution stated as conclusions; reason: ALG is the cost of the actual run, not an assumed trace
--   - encoding: costs and OPT on the line → ℝ≥0∞ costs, ⊤ for infeasible, OPT the infimum over all finite schedules; reason: Section 2's conventions
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), pp. 22–24, Theorem B.2 and its proof; pp. 21–22, Appendix B; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_RootedLine

namespace MLAMaxDelay.RandomizedTimer.Supplement

/-- Theorem B.2, pp. 22–24. Max-Balance is well defined on every rooted-line input (its
execution exists, is unique and clears every request), and its competitive ratio over inputs
with exactly `N` requests is `Θ(log(N+1))`: uniform constants `0 < c`, `0 < C` with the upper
bound on every such input and a matching lower-bound input for every `N ≥ 1`. -/
theorem max_balance_log_ratio :
    (∀ I : LineInput, ∃ S : LineSchedule, IsMaxBalanceRun I S ∧ LineFeasible I S ∧
      ∀ S' : LineSchedule, IsMaxBalanceRun I S' → S' = S) ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∀ I : LineInput, I.requests.card = N → ∀ S : LineSchedule, IsMaxBalanceRun I S →
        lineCost I S ≤ ENNReal.ofReal (C * Real.log (N + 1)) * lineOptimum I) ∧
      (∃ I : LineInput, I.requests.card = N ∧ ∀ S : LineSchedule, IsMaxBalanceRun I S →
        ENNReal.ofReal (c * Real.log (N + 1)) * lineOptimum I ≤ lineCost I S) := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
