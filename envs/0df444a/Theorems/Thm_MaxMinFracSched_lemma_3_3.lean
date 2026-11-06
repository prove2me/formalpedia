-- Prove2me | Theorems.Thm_MaxMinFracSched_lemma_3_3
-- name    : MaxMinFracSched.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:09.336133+00:00
-- url     : https://prove2.me/theorems/d7c86d7a-3930-415a-b27f-c17ed287c38d
-- title:
--   Lemma 3.3 — EDF schedulability
-- statement:
--   Let $J$ be a finite set of jobs with $a_i<d_i$ and $w_i>0$ for every $i\in J$.
--
--   1. If $W_J([L,R])\le R-L$ for every interval $[L,R]$, then an EDF run on $J$ exists, and every EDF run (with any tie-breaking) completes every job by its deadline: $c_i(d_i)=w_i$ for all $i\in J$.
--   2. If $W_J([L,R])>R-L$ for some interval $[L,R]$, then every schedule leaves some job incomplete at its deadline: $c_i(d_i)<w_i$ for some $i\in J$.
--
--   This folklore characterization of EDF schedulability is the basis of the densest-interval formula for the offline optimum (Corollary 3.4).
--
--   Differences from the source:
--   - generalization: a schedule runs one job at a time with preemption → IsSchedule: measurable rates r_j(t) ≥ 0 with Σ_{j∈J} r_j(t) ≤ 1; reason: one-job-at-a-time schedules are the {0,1}-valued rate schedules, so the statement over all rate schedules contains the source's statement
--   - reading: works on the job with earliest deadline (breaking ties arbitrarily) → any eligible job of earliest deadline may be served at each time, independently; the rule holds for almost every t; reason: the strongest reading of 'arbitrarily' (every tie-breaking rule is a special case); a schedule matters only up to null sets
--   - reading: eligible jobs: c_i < α′ · f̂(t) · w_i → eligible jobs also satisfy a_j ≤ t < d_j; reason: only released jobs can be worked on, and work after the deadline does not count; the paper never serves an expired job
--   - reading: EDF can complete all jobs before their deadlines → an EDF run exists and every EDF run completes every job; reason: existence keeps the clause non-vacuous; 'every run' is the strongest reading of EDF with arbitrary tie-breaking
--   - encoding: a job set J (jobs with a_i < d_i, w_i > 0) → Finset Job, every job with a < d and 0 < w, possibly empty; reason: labels only allow repeated triples; the empty set is a trivial extra case
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 3.3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_workIn
import Definitions.Def_MaxMinFracSched_IsSchedule
import Definitions.Def_MaxMinFracSched_work
import Definitions.Def_MaxMinFracSched_IsThresholdEDF
import Definitions.Def_MaxMinFracSched_IsEDF

namespace MaxMinFracSched

/-- **Lemma 3.3 (EDF schedulability).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 3.3, p.12 (PDF p.14): "Consider a job set J.
If W([L, R]) ≤ R−L for all intervals [L, R], then EDF can complete all jobs before their
deadlines. If this condition is not true, then no algorithm can schedule all jobs to completion
before their deadline."

**Formalization Note.** Jobs satisfy `a < d` and `0 < w` (the paper's standing assumption); `J`
may be empty. Clause (i): if every interval `[L, R]` has `W_J([L, R]) ≤ R − L`, then an EDF run
exists and every EDF run (any tie-breaking) completes every job, `c_j(d_j) = w_j`. Clause (ii):
if some interval has `W_J([L, R]) > R − L`, every feasible schedule leaves some job with
`c_j(d_j) < w_j`. Schedules are rate schedules (`IsSchedule`). -/
theorem lemma_3_3 (J : Finset Job) (hJ : ∀ j ∈ J, j.a < j.d ∧ 0 < j.w) :
    ((∀ L R : ℝ, L ≤ R → workIn J L R ≤ R - L) →
      (∃ r, IsEDF J r) ∧ ∀ r, IsEDF J r → ∀ j ∈ J, work r j j.d = j.w) ∧
    ((∃ L R : ℝ, L ≤ R ∧ R - L < workIn J L R) →
      ∀ r, IsSchedule J r → ∃ j ∈ J, work r j j.d < j.w) := by sorry

end MaxMinFracSched
