-- Prove2me | Theorems.Thm_MaxMinFracSched_corollary_3_4
-- name    : MaxMinFracSched.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:15.329658+00:00
-- url     : https://prove2.me/theorems/f8a9cad6-322e-47fe-b333-fa1630a7ca9f
-- title:
--   Corollary 3.4 — $\hat f=\min(1/\rho^\star,1)$ and the form of densest intervals
-- statement:
--   Let $J$ be a valid instance and $\rho^\star=\sup_{L<R}\rho_J([L,R])$ its maximal work density. Then
--
--   1. the offline optimum is
--   $$\hat f_J=\min\Bigl(\frac1{\rho^\star},\,1\Bigr);$$
--   2. the maximal density is attained on an interval $[a_i,d_{i'}]$ for some jobs $i,i'\in J$ with $a_i<d_{i'}$;
--   3. every interval $[L,R]$, $L<R$, of maximal density has the form $L=a_i$, $R=d_{i'}$ for some jobs $i,i'\in J$.
--
--   The formula reduces the offline benchmark to a finite computation over arrival–deadline pairs; it is how the optimum of the hard family is computed (Lemma 6.2).
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: labels only allow repeated triples; nonemptiness and validity are the paper's standing assumptions
--   - encoding: f̂_J, the value of an optimal offline schedule → optVal J: sSup of v ∈ [0,1] such that some rate schedule gives every job ≥ v; reason: same value: rate schedules do not beat EDF on the scaled works, which is a one-job-at-a-time schedule (Lemma 3.3), and fractional completions never exceed 1
--   - reading: without loss of generality the densest interval has the form I⋆ = [a_i, d_i′] → (2) some maximal-density interval is [a_i, d_i′]; (3) every maximal-density interval is [a_i, d_i′]; reason: (2)+(3) is the strong reading; Definition 3.2's inclusion-maximality then holds automatically for the densest interval
--   - encoding: ρ⋆, the density of the densest interval → maxDensity J: sSup of ρ_J([L,R]) over L < R; reason: the supremum is attained (clause 2), so it is the maximum
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Corollary 3.4, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_optVal
import Definitions.Def_MaxMinFracSched_density
import Definitions.Def_MaxMinFracSched_maxDensity

namespace MaxMinFracSched

/-- **Corollary 3.4 (the densest-interval formula).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Corollary 3.4, p.13 (PDF p.15):
"Given a set of jobs J, if the densest interval I⋆ has density ρ⋆, then max-min fractional
scheduling has objective value f̂ = min(1/ρ⋆, 1). Furthermore, without loss of generality the
densest interval has the form I⋆ = [ai, di′] for some jobs i, i′ in J."

**Formalization Note.** For a valid instance: (i) `f̂_J = min(1/ρ⋆, 1)`, with `f̂_J` the
supremum over feasible schedules (`optVal`) and `ρ⋆` the supremum of the densities of
nondegenerate intervals (`maxDensity`); (ii) the maximal density is attained on an interval
`[a_i, d_{i′}]` of jobs `i, i′ ∈ J`; (iii) every interval of maximal density has this form. -/
theorem corollary_3_4 (J : Finset Job) (hJ : ValidInstance J) :
    optVal J = min (1 / maxDensity J) 1 ∧
    (∃ i ∈ J, ∃ i' ∈ J, i.a < i'.d ∧ density J i.a i'.d = maxDensity J) ∧
    (∀ L R : ℝ, L < R → density J L R = maxDensity J →
      ∃ i ∈ J, ∃ i' ∈ J, L = i.a ∧ R = i'.d) := by sorry

end MaxMinFracSched
