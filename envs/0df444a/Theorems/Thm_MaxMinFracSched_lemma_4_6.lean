-- Prove2me | Theorems.Thm_MaxMinFracSched_lemma_4_6
-- name    : MaxMinFracSched.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:15.531628+00:00
-- url     : https://prove2.me/theorems/e698aaeb-cb1b-4cb9-b544-85525487ed8e
-- title:
--   Lemma 4.6 — OPT is never idle
-- statement:
--   Let $J$ be a valid instance and $r$ a ScaledEDF$(\alpha')$ run on $J$ that is not $\alpha'$-competitive (some job has $f_j<\alpha'\hat f_J$). Then there are a valid instance $J'$ and a ScaledEDF$(\alpha')$ run $r'$ on $J'$ such that
--
--   1. $r'$ is not $\alpha'$-competitive on $J'$ ($J'$ is *harder*, Definition 4.4);
--   2. every $\hat f$-EDF run on $J'$ is never idle between the first arrival and the final deadline of $J'$;
--   3. if $(J,r)$ has the last-job-critical property, so does $(J',r')$;
--   4. for every $\varepsilon$, if all jobs of $J$ have work at most $\varepsilon$, so do all jobs of $J'$.
--
--   This is the first transformation of the upper-bound proof: it removes the idle periods of the optimal schedule while keeping the instance hard for ScaledEDF.
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: labels only allow repeated triples; nonemptiness and validity are the paper's standing assumptions
--   - encoding: f̂_J, the value of an optimal offline schedule → optVal J: sSup of v ∈ [0,1] such that some rate schedule gives every job ≥ v; reason: same value: rate schedules do not beat EDF on the scaled works, which is a one-job-at-a-time schedule (Lemma 3.3), and fractional completions never exceed 1
--   - encoding: c_i ≤ w_i, the work completed on job i by its deadline → min(w_j, ∫_{a_j}^{d_j} r_j) as the completed work; reason: work after the deadline does not count and work beyond w_i is not counted; same values
--   - reading: works on the job with earliest deadline (breaking ties arbitrarily) → any eligible job of earliest deadline may be served at each time, independently; the rule holds for almost every t; reason: the strongest reading of 'arbitrarily' (every tie-breaking rule is a special case); a schedule matters only up to null sets
--   - reading: eligible jobs: c_i < α′ · f̂(t) · w_i → eligible jobs also satisfy a_j ≤ t < d_j; reason: only released jobs can be worked on, and work after the deadline does not count; the paper never serves an expired job
--   - encoding: ScaledEDF is not α′-competitive on J (and on J′) → a given ScaledEDF(α′) run r on J and some run r′ on J′ with a job below α′ · f̂; reason: with arbitrary tie-breaking, 'not α′-competitive' means some run fails
--   - encoding: Fix some α′ > 0 (Section 4) → no hypothesis on α′; reason: α′ > 0 is implied by the failing run, since fractional completions are ≥ 0 and f̂ ≥ 0
--   - encoding: OPT (as scheduled by f̂-EDF) is never idle on [0, T] → OptNeverIdle J′: every f̂-EDF run has Σ_j r_j(t) = 1 for a.e. t in [first arrival, final deadline]; reason: the paper's clock starts at the first arrival
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 4.6, p.15 (PDF p.17); Definition 4.4, p.15

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_IsScaledEDF
import Definitions.Def_MaxMinFracSched_ScaledFails
import Definitions.Def_MaxMinFracSched_OptNeverIdle
import Definitions.Def_MaxMinFracSched_LastJobCritical

namespace MaxMinFracSched

/-- **Lemma 4.6 (OPT is Never Idle).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 4.6, p.15 (PDF p.17): "Given any input instance
J we can construct a harder instance J′ where OPT (as scheduled by f̂-EDF) is never idle.
Furthermore, if J has the last job critical property, then so does J′, and if all jobs in J are of
at length at most ε, then so are all jobs in J′."

"Harder" is Definition 4.4, p.15: "Consider an instance J where ScaledEDF is not α′-competitive.
We say that job set J′ is harder than J when ScaledEDF is not α′-competitive on J′."

**Formalization Note.** Given a valid instance `J` and a ScaledEDF(α′) run `r` on it that is not
α′-competitive, there are a valid instance `J′` and a ScaledEDF(α′) run `r′` on it
that is not α′-competitive, such that every `f̂`-EDF run of `J′` is never idle between the first
arrival and the final deadline, the last-job-critical property passes from `(J, r)` to `(J′, r′)`,
and every bound `ε` on the works of `J` is a bound on the works of `J′`. The standing assumption
`α′ > 0` of Section 4 is implied by the failing run (fractional completions are `≥ 0`). -/
theorem lemma_4_6 (α' : ℝ) (J : Finset Job) (hJ : ValidInstance J)
    (r : Job → ℝ → ℝ) (hr : IsScaledEDF α' J r) (hfail : ScaledFails α' J r) :
    ∃ J', ValidInstance J' ∧ ∃ r', IsScaledEDF α' J' r' ∧ ScaledFails α' J' r' ∧
      OptNeverIdle J' ∧ (LastJobCritical α' J r → LastJobCritical α' J' r') ∧
      ∀ ε : ℝ, (∀ j ∈ J, j.w ≤ ε) → ∀ j ∈ J', j.w ≤ ε := by sorry

end MaxMinFracSched
