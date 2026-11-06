-- Prove2me | Theorems.Thm_MaxMinFracSched_theorem_1_1
-- name    : MaxMinFracSched.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:53.079209+00:00
-- url     : https://prove2.me/theorems/4f6a44ea-9512-42b5-8c9f-c8aa7d3084c2
-- title:
--   Theorem 1.1 (competitive-ratio clauses) — ScaledEDF(1/2) is 1/2-competitive and no online algorithm beats 1/2
-- statement:
--   1. There is a deterministic online algorithm whose schedule on every valid instance is a ScaledEDF$(1/2)$ run.
--   2. On every valid instance $J$, every ScaledEDF$(1/2)$ run (with any tie-breaking) gives every job
--   $$f_j\ \ge\ \tfrac12\,\hat f_J .$$
--   3. For every randomized online algorithm $(\mathrm{ALG}_\omega)$ on any probability space, where the instance is fixed before the random bits are drawn (oblivious adversary), and every $\alpha>1/2$, there is a valid instance $J$ with
--   $$\mathbb E_\omega\Bigl[\min_{j\in J}f_j\bigl(\mathrm{ALG}_\omega(J)\bigr)\Bigr]<\alpha\,\hat f_J .$$
--   Deterministic algorithms are the case of a one-point probability space.
--
--   Together, ScaledEDF$(1/2)$ attains the best possible competitive ratio $1/2$ for max-min fractional scheduling, and randomization does not help. The third sentence of the printed theorem ("ScaledEDF can be implemented with worst-case $O(\log^3 n)$ time per job arrival") is the separate computational result Theorem 8.1 and is not formalized in this mission.
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: labels only allow repeated triples; nonemptiness and validity are the paper's standing assumptions
--   - encoding: f̂_J, the value of an optimal offline schedule → optVal J: sSup of v ∈ [0,1] such that some rate schedule gives every job ≥ v; reason: same value: rate schedules do not beat EDF on the scaled works, which is a one-job-at-a-time schedule (Lemma 3.3), and fractional completions never exceed 1
--   - encoding: c_i ≤ w_i, the work completed on job i by its deadline → min(w_j, ∫_{a_j}^{d_j} r_j) as the completed work; reason: work after the deadline does not count and work beyond w_i is not counted; same values
--   - generalization: a schedule runs one job at a time with preemption → IsSchedule: measurable rates r_j(t) ≥ 0 with Σ_{j∈J} r_j(t) ≤ 1; reason: one-job-at-a-time schedules are the {0,1}-valued rate schedules, so the statement over all rate schedules contains the source's statement
--   - reading: works on the job with earliest deadline (breaking ties arbitrarily) → any eligible job of earliest deadline may be served at each time, independently; the rule holds for almost every t; reason: the strongest reading of 'arbitrarily' (every tie-breaking rule is a special case); a schedule matters only up to null sets
--   - reading: eligible jobs: c_i < α′ · f̂(t) · w_i → eligible jobs also satisfy a_j ≤ t < d_j; reason: only released jobs can be worked on, and work after the deadline does not count; the paper never serves an expired job
--   - encoding: online: nothing is known about job i until its arrival time a_i → OnlineAlg.causal: if J_{≤t} = J'_{≤t}, the work on each job of J_{≤t} by every time s ≤ t agrees; reason: the weakest form of online-ness, which makes the class of online algorithms as large as possible
--   - encoding: a randomized scheduler against an oblivious adversary → RandOnlineAlg Ω: a family of OnlineAlg indexed by ω with rates jointly measurable in (ω, t); the instance is chosen before ω; reason: joint measurability only excludes schedulers whose expected objective is undefined
--   - encoding: ScaledEDF(1/2) is a … deterministic online algorithm → there is an OnlineAlg whose schedule on every valid instance is a ScaledEDF(1/2) run; reason: a ScaledEDF run with a fixed tie-breaking rule is a causal deterministic algorithm
--   - encoding: no online algorithm achieves competitive ratio > 1/2 → for every α > 1/2 some valid instance has E[min_j f_j] < α · f̂_J; reason: the negation of 'some α > 1/2 has E[min_j f_j] ≥ α f̂_J on every instance'
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 1.1, p.3 (PDF p.5); restated p.28 (PDF p.30)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_minFrac
import Definitions.Def_MaxMinFracSched_optVal
import Definitions.Def_MaxMinFracSched_IsScaledEDF
import Definitions.Def_MaxMinFracSched_OnlineAlg
import Definitions.Def_MaxMinFracSched_RandOnlineAlg

namespace MaxMinFracSched

/-- **Theorem 1.1 (competitive-ratio clauses).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 1.1, p.3 (PDF p.5; restated p.28,
PDF p.30): "ScaledEDF(1/2) is a 1/2-competitive deterministic online algorithm for the max-min
fractional scheduling problem. Furthermore, there is no online algorithm (deterministic or
randomized, even against an oblivious adversary) that achieves competitive ratio > 1/2."

Three conjuncts:
1. there is a deterministic online algorithm whose schedule on every valid instance is a
   ScaledEDF(1/2) run;
2. every ScaledEDF(1/2) run (any tie-breaking) on every valid instance `J` gives every job
   fractional completion at least `½ · f̂_J`;
3. for every randomized online algorithm (on any probability space; the instance is fixed before
   the randomness, which is the oblivious adversary) and every `α > 1/2`, some valid instance `J`
   has `E[min_{j∈J} f_j] < α · f̂_J`.

**Formalization Note.** Deterministic algorithms are the case of a Dirac measure. Schedules are
rate schedules, online algorithms are causal on cumulative work, randomized algorithms are
jointly measurable. The third sentence of the printed theorem ("ScaledEDF can be implemented with
worst-case O(log³ n) time per job arrival") is the separate computational result Theorem 8.1 and
is not formalized here. -/
theorem theorem_1_1 :
    (∃ A : OnlineAlg, ∀ J, ValidInstance J → IsScaledEDF (1 / 2) J (A.sched J)) ∧
    (∀ J, ValidInstance J → ∀ r, IsScaledEDF (1 / 2) J r →
      ∀ j ∈ J, (1 / 2 : ℝ) * optVal J ≤ frac r j) ∧
    (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (A : RandOnlineAlg Ω) (α : ℝ), 1 / 2 < α →
      ∃ J, ValidInstance J ∧ ∫ ω, minFrac J ((A.alg ω).sched J) ∂μ < α * optVal J) := by sorry

end MaxMinFracSched
