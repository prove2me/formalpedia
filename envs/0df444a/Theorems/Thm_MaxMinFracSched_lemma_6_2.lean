-- Prove2me | Theorems.Thm_MaxMinFracSched_lemma_6_2
-- name    : MaxMinFracSched.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:45.58148+00:00
-- url     : https://prove2.me/theorems/b897d9d3-98bd-4210-ae9a-5ab25e1115c0
-- title:
--   Lemma 6.2 — $\hat f_{J^{(i)}}=x^{i-1}$ on the hard family (corrected: display (10))
-- statement:
--   Let $k\ge1$, $0<x<1$, and let $J^{(i)}$, $1\le i\le k$, be the prefix instances of the hard family (jobs released at $t_0,\dots,t_{i-1}$, with the works $w_m(j)$ of display (10) as corrected). Then
--   $$\hat f_{J^{(i)}}=x^{\,i-1}\qquad(1\le i\le k).$$
--
--   The offline optimum drops by the factor $x$ at each release, while an online algorithm must already have served the jobs due at $t_i$ before it learns whether the adversary stops; this mismatch is the source of the lower bound $1/2$.
--
--   Differences from the source:
--   - encoding: f̂_J, the value of an optimal offline schedule → optVal J: sSup of v ∈ [0,1] such that some rate schedule gives every job ≥ v; reason: same value: rate schedules do not beat EDF on the scaled works, which is a one-job-at-a-time schedule (Lemma 3.3), and fractional completions never exceed 1
--   - correction: display (10): w_i(j) = T_j if i = 1; (1−x)/x^j · Σ_{ℓ=1}^{i+1} T_ℓ if j = i+1; (1−x)/x^j · T_j otherwise → w_0(j) = T_j; for i ≥ 1, w_i(i+1) = (1−x)/x^i · Σ_{ℓ=1}^{i+1} T_ℓ and w_i(j) = (1−x)/x^i · T_j for j ≥ i+2; reason: as printed the lemma is false: (10) puts the release at t_0 under its second and third cases, so k = 3, x = 1/2 (t = (0, 1/4, 1/2, 1), T = (1/4, 1/4, 1/2)) give w_0(1), w_0(2), w_0(3) = 1/4, 1/2, 2, density 11/4 on [0,1] and f̂_{J^{(1)}} = 4/11 ≠ x^0 = 1; even with w_0(j) = T_j from the sentence on p.29, the printed case i = 1 gives w_1(2) = 1/4, w_1(3) = 1/2, so J^{(2)} has densities 1, 3/2, 7/4, 1, 1 on [0,1/4], [0,1/2], [0,1], [1/4,1/2], [1/4,1] and f̂_{J^{(2)}} = 4/7 ≠ 1/2; the corrected family is the one of Figure 3 and of the proof of Lemma 6.2
--   - encoding: the jobs of the family → hardJob x k i j = ⟨pair(i, j), t_i, t_j, w_i(j)⟩ and J^{(i)} = hardPrefix x k i; reason: labels make distinct index pairs distinct jobs, so the prefixes are literal subsets
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 6.2, p.30 (PDF p.32); family: Section 6.1, display (10) and Figure 3, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_optVal
import Definitions.Def_MaxMinFracSched_hardPrefix

namespace MaxMinFracSched

/-- **Lemma 6.2 (OPT on the hard family).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 6.2, p.30 (PDF p.32): "Let J an instance
of our hard family with k intervals and fixed x < 1. For any i > 0, OPT achieves fractional
completion exactly x^{i−1} on J(i), i.e. f̂J(i) = x^{i−1}."

**Formalization Note.** The family is display (10) as corrected (see `hw`): as printed, `k = 3`,
`x = 1/2`, `i = 1` give `f̂_{J^{(1)}} = 4/11 ≠ 1` (and `i = 2` gives `4/7 ≠ 1/2` even with
`w_0(j) = T_j` from the sentence on p.29). Parameters: `k ≥ 1`, `0 < x < 1`,
`1 ≤ i ≤ k`. -/
theorem lemma_6_2 (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (i : ℕ)
    (hi1 : 1 ≤ i) (hik : i ≤ k) :
    optVal (hardPrefix x k i) = x ^ (i - 1) := by sorry

end MaxMinFracSched
