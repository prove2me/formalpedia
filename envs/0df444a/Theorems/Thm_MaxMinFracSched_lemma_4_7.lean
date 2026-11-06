-- Prove2me | Theorems.Thm_MaxMinFracSched_lemma_4_7
-- name    : MaxMinFracSched.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:08.99197+00:00
-- url     : https://prove2.me/theorems/414b0f01-704e-496c-b8dc-e983090c9725
-- title:
--   Lemma 4.7 — last job critical
-- statement:
--   Let $J$ be a valid instance and $r$ a ScaledEDF$(\alpha')$ run on $J$ that is not $\alpha'$-competitive. Then there are a valid instance $J'$ and a ScaledEDF$(\alpha')$ run $r'$ on $J'$ such that
--
--   1. some job $\ell$ of latest deadline in $J'$ has $f_\ell<\alpha'\hat f_{J'}$ (the last job is critical);
--   2. consequently $r'$ is not $\alpha'$-competitive on $J'$;
--   3. $r'$ is never idle between the first arrival and the final deadline of $J'$;
--   4. for every $\varepsilon$, if all deadlines of $J$ lie in $[T-\varepsilon,T]$, where $T$ is the final deadline of $J$, then all deadlines of $J'$ lie within $\varepsilon$ of the final deadline of $J'$.
--
--   Once ScaledEDF fails on some job, the rest of the instance can be discarded; the lemma isolates the failing job as the last one.
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: labels only allow repeated triples; nonemptiness and validity are the paper's standing assumptions
--   - encoding: f̂_J, the value of an optimal offline schedule → optVal J: sSup of v ∈ [0,1] such that some rate schedule gives every job ≥ v; reason: same value: rate schedules do not beat EDF on the scaled works, which is a one-job-at-a-time schedule (Lemma 3.3), and fractional completions never exceed 1
--   - encoding: c_i ≤ w_i, the work completed on job i by its deadline → min(w_j, ∫_{a_j}^{d_j} r_j) as the completed work; reason: work after the deadline does not count and work beyond w_i is not counted; same values
--   - reading: works on the job with earliest deadline (breaking ties arbitrarily) → any eligible job of earliest deadline may be served at each time, independently; the rule holds for almost every t; reason: the strongest reading of 'arbitrarily' (every tie-breaking rule is a special case); a schedule matters only up to null sets
--   - reading: eligible jobs: c_i < α′ · f̂(t) · w_i → eligible jobs also satisfy a_j ≤ t < d_j; reason: only released jobs can be worked on, and work after the deadline does not count; the paper never serves an expired job
--   - reading: Given any instance J where ScaledEDF fails to be α-competitive → a ScaledEDF(α′) run r on J that is not α′-competitive; reason: Section 4 sets α = α′ ('if α′ = 1/2 … ScaledEDF achieves competitive ratio α = 1/2'); the lemma's own conclusion speaks of α′
--   - encoding: Fix some α′ > 0 (Section 4) → no hypothesis on α′; reason: α′ > 0 is implied by the failing run, since fractional completions are ≥ 0 and f̂ ≥ 0
--   - reading: the final job → some job of latest deadline in J′; reason: with ties in the latest deadline, 'the final job' is any job of latest deadline
--   - encoding: on J′, ScaledEDF is never idle → Σ_j r′_j(t) = 1 for a.e. t in [first arrival, final deadline] of J′; reason: the paper's clock starts at the first arrival
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 4.7, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_IsScaledEDF
import Definitions.Def_MaxMinFracSched_ScaledFails
import Definitions.Def_MaxMinFracSched_LastJobCritical
import Definitions.Def_MaxMinFracSched_ScaledNeverIdle
import Definitions.Def_MaxMinFracSched_maxDl

namespace MaxMinFracSched

/-- **Lemma 4.7 (Last Job Critical).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 4.7, p.16 (PDF p.18): "Given any instance J
where ScaledEDF fails to be α-competitive, we can construct an instance J′ where ScaledEDF fails
to complete an α′ · f̂ fraction of the final job. Consequently, ScaledEDF must fail to be
α′-competitive on J′. Furthermore, on J′, ScaledEDF is never idle and if all deadlines are within
ε of the final deadline in J then so are all deadlines in J′."

**Formalization Note.** "Fails to be α-competitive" is read with `α = α′`, as
everywhere in Section 4. Given a valid instance `J` and a ScaledEDF(α′) run `r` on it that is not
α′-competitive, there are a valid `J′` and a ScaledEDF(α′) run `r′` on it in which some job of
latest deadline gets less than `α′ · f̂_{J′}`, which is not α′-competitive, which keeps the
processor busy at almost every time between the first arrival and the final deadline of `J′`,
and such that every `ε` for which all deadlines of `J` lie within `ε` of its final deadline has
the same property for `J′`. The standing assumption `α′ > 0` of Section 4 is implied by the
failing run (fractional completions are `≥ 0`). -/
theorem lemma_4_7 (α' : ℝ) (J : Finset Job) (hJ : ValidInstance J)
    (r : Job → ℝ → ℝ) (hr : IsScaledEDF α' J r) (hfail : ScaledFails α' J r) :
    ∃ J', ValidInstance J' ∧ ∃ r', IsScaledEDF α' J' r' ∧ LastJobCritical α' J' r' ∧
      ScaledFails α' J' r' ∧ ScaledNeverIdle J' r' ∧
      ∀ ε : ℝ, (∀ j ∈ J, maxDl J - ε ≤ j.d) → ∀ j ∈ J', maxDl J' - ε ≤ j.d := by sorry

end MaxMinFracSched
