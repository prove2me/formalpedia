-- Prove2me | Theorems.Thm_MaxMinFracSched_eq_14
-- name    : MaxMinFracSched.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:09.559998+00:00
-- url     : https://prove2.me/theorems/8f7ecec6-9575-459e-8f6c-a45a045971ea
-- title:
--   Eq. (14) — an $\alpha$-competitive online algorithm on the hard family has $\alpha\le 1/(1+x-x^k)$ (corrected: display (10))
-- statement:
--   Let $k\ge1$, $0<x<1$ and let $\mathrm{ALG}$ be a deterministic online algorithm. If $\mathrm{ALG}$ is $\alpha$-competitive on every prefix instance of the hard family, i.e.
--   $$f_j\bigl(\mathrm{ALG}(J^{(i)})\bigr)\ge\alpha\,\hat f_{J^{(i)}}\qquad\text{for all }1\le i\le k\text{ and }j\in J^{(i)},$$
--   then
--   $$\alpha\le\frac{1}{1+x-x^k}.$$
--
--   Letting $x\to1$ and then $k\to\infty$ gives $\alpha\le1/2$: this is the deterministic, adaptive-adversary core of the impossibility half of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: a schedule runs one job at a time with preemption → IsSchedule: measurable rates r_j(t) ≥ 0 with Σ_{j∈J} r_j(t) ≤ 1; reason: one-job-at-a-time schedules are the {0,1}-valued rate schedules, so the statement over all rate schedules contains the source's statement
--   - encoding: f̂_J, the value of an optimal offline schedule → optVal J: sSup of v ∈ [0,1] such that some rate schedule gives every job ≥ v; reason: same value: rate schedules do not beat EDF on the scaled works, which is a one-job-at-a-time schedule (Lemma 3.3), and fractional completions never exceed 1
--   - encoding: c_i ≤ w_i, the work completed on job i by its deadline → min(w_j, ∫_{a_j}^{d_j} r_j) as the completed work; reason: work after the deadline does not count and work beyond w_i is not counted; same values
--   - encoding: online: nothing is known about job i until its arrival time a_i → OnlineAlg.causal: if J_{≤t} = J'_{≤t}, the work on each job of J_{≤t} by every time s ≤ t agrees; reason: the weakest form of online-ness, which makes the class of online algorithms as large as possible
--   - correction: the hard family of display (10) as printed → the corrected works w_m(j) (see Lemma 6.2's correction); reason: the page's derivation of (13) uses Lemma 6.2 and (11)–(12), which hold only for the corrected family
--   - encoding: any α-competitive ALG facing the adaptive adversary that may stop after any t_i → ALG α-competitive on every prefix instance J^{(i)}, 1 ≤ i ≤ k; reason: a deterministic ALG faces each possible stopping point; that is exactly competitiveness on every prefix
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 6.3, Eqs. (13)–(14), p.32 (PDF p.34)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_optVal
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_OnlineAlg
import Definitions.Def_MaxMinFracSched_hardPrefix

namespace MaxMinFracSched

/-- **Section 6.3, (14): the bound for a fixed family.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 6.3, p.32 (PDF p.34):
"Because all jobs in J(k) are due by time tk = 1, the work WALG cannot exceed one. From (13)
together with WALG ≤ 1 we therefore obtain α ≤ 1/(1 + x − x^k). (14)"

**Formalization Note.** A deterministic online algorithm that is α-competitive on every prefix
instance `J^{(i)}`, `1 ≤ i ≤ k`, of the corrected hard family (every job of `J^{(i)}` receives at
least `α · f̂_{J^{(i)}}`) has `α ≤ 1/(1 + x − x^k)`. This is the adaptive adversary of p.29,
which may stop after any `t_i`. Parameters `k ≥ 1`, `0 < x < 1`. -/
theorem eq_14 (A : OnlineAlg) (k : ℕ) (x α : ℝ) (hk : 1 ≤ k) (hx0 : 0 < x) (hx1 : x < 1)
    (hA : ∀ i, 1 ≤ i → i ≤ k → ∀ j ∈ hardPrefix x k i,
      α * optVal (hardPrefix x k i) ≤ frac (A.sched (hardPrefix x k i)) j) :
    α ≤ 1 / (1 + x - x ^ k) := by sorry

end MaxMinFracSched
