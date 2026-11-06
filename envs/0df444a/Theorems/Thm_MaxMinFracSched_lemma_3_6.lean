-- Prove2me | Theorems.Thm_MaxMinFracSched_lemma_3_6
-- name    : MaxMinFracSched.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:03.28814+00:00
-- url     : https://prove2.me/theorems/d94200bf-5980-4d33-94d4-7e5805de047a
-- title:
--   Lemma 3.6 — small jobs suffice for ScaledEDF
-- statement:
--   Fix $\alpha'>0$, $\alpha\in\mathbb R$ and $\varepsilon>0$. Suppose that on every valid instance whose jobs all have work $w_j\le\varepsilon$, every ScaledEDF$(\alpha')$ run gives every job fractional completion $f_j\ge\alpha\,\hat f_J$. Then on every valid instance $J$, every ScaledEDF$(\alpha')$ run gives every job $f_j\ge\alpha\,\hat f_J$.
--
--   The lemma lets the analysis of ScaledEDF assume arbitrarily small jobs while still concluding about ScaledEDF itself, not about a modified algorithm (contrast Observation 3.5).
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: labels only allow repeated triples; nonemptiness and validity are the paper's standing assumptions
--   - encoding: f̂_J, the value of an optimal offline schedule → optVal J: sSup of v ∈ [0,1] such that some rate schedule gives every job ≥ v; reason: same value: rate schedules do not beat EDF on the scaled works, which is a one-job-at-a-time schedule (Lemma 3.3), and fractional completions never exceed 1
--   - encoding: c_i ≤ w_i, the work completed on job i by its deadline → min(w_j, ∫_{a_j}^{d_j} r_j) as the completed work; reason: work after the deadline does not count and work beyond w_i is not counted; same values
--   - reading: works on the job with earliest deadline (breaking ties arbitrarily) → any eligible job of earliest deadline may be served at each time, independently; the rule holds for almost every t; reason: the strongest reading of 'arbitrarily' (every tie-breaking rule is a special case); a schedule matters only up to null sets
--   - reading: eligible jobs: c_i < α′ · f̂(t) · w_i → eligible jobs also satisfy a_j ≤ t < d_j; reason: only released jobs can be worked on, and work after the deadline does not count; the paper never serves an expired job
--   - reading: α-competitive when all jobs are size at most ε → the hypothesis is for one fixed ε > 0; reason: a single size bound is a weaker hypothesis than 'for arbitrarily small ε', so the lemma is the stronger one
--   - encoding: ScaledEDF(α′) is α-competitive → every ScaledEDF(α′) run gives every job f_j ≥ α · f̂_J; reason: f_J = min_j f_j; arbitrary tie-breaking means every run
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 3.6, p.13 (PDF p.15); proof via Lemma A.1, p.57 (PDF p.59)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_optVal
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_IsScaledEDF

namespace MaxMinFracSched

/-- **Lemma 3.6 (Small Jobs for ScaledEDF).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 3.6, p.13 (PDF p.15; proof via
Lemma A.1, p.57): "If ScaledEDF(α′) is α-competitive when all jobs are size at most ε, then it is
α-competitive."

**Formalization Note.** "ScaledEDF(α′) is α-competitive on `J`" means every ScaledEDF(α′) run
(any tie-breaking) gives every job fractional completion at least `α · f̂_J`. The hypothesis is
for one fixed `ε > 0` (a single bound on job sizes suffices). `α′ > 0` is the standing assumption
of Section 4 ("Fix some α′ > 0", p.14). -/
theorem lemma_3_6 (α' α ε : ℝ) (hα' : 0 < α') (hε : 0 < ε)
    (hsmall : ∀ J, ValidInstance J → (∀ j ∈ J, j.w ≤ ε) →
      ∀ r, IsScaledEDF α' J r → ∀ j ∈ J, α * optVal J ≤ frac r j) :
    ∀ J, ValidInstance J → ∀ r, IsScaledEDF α' J r → ∀ j ∈ J, α * optVal J ≤ frac r j := by sorry

end MaxMinFracSched
