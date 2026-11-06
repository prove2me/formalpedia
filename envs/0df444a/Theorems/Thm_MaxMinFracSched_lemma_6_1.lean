-- Prove2me | Theorems.Thm_MaxMinFracSched_lemma_6_1
-- name    : MaxMinFracSched.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:08.341188+00:00
-- url     : https://prove2.me/theorems/659ae92d-5f7e-4738-87f2-ea846459c141
-- title:
--   Lemma 6.1 — randomized to deterministic reduction
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $(\mathrm{ALG}_\omega)$ a randomized online algorithm, $\mathcal J$ a set of valid instances, $b_J(j)>0$ a benchmark for every job $j$ of every $J\in\mathcal J$, and $\alpha\in\mathbb R$. If
--   $$\mathbb E_\omega\Bigl[\min_{j\in J}\frac{f_j(\mathrm{ALG}_\omega(J))}{b_J(j)}\Bigr]\ge\alpha\qquad\text{for every }J\in\mathcal J,$$
--   then there is a deterministic online algorithm $\mathrm{ALG}'$ with
--   $$\frac{f_j(\mathrm{ALG}'(J))}{b_J(j)}\ge\alpha\qquad\text{for every }J\in\mathcal J\text{ and every }j\in J.$$
--
--   With $b_J(j)=\hat f_J$ this is the max-min objective; with $b_J(j)=\hat f_j$, the lexicographic optimum of job $j$, it is the lexicographic objective, whose competitive ratio is $\min_{i\in J}f_i/\hat f_i$. The lemma transfers deterministic impossibility results to randomized algorithms against an oblivious adversary.
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: labels only allow repeated triples; nonemptiness and validity are the paper's standing assumptions
--   - encoding: c_i ≤ w_i, the work completed on job i by its deadline → min(w_j, ∫_{a_j}^{d_j} r_j) as the completed work; reason: work after the deadline does not count and work beyond w_i is not counted; same values
--   - encoding: a randomized scheduler against an oblivious adversary → RandOnlineAlg Ω: a family of OnlineAlg indexed by ω with rates jointly measurable in (ω, t); the instance is chosen before ω; reason: joint measurability only excludes schedulers whose expected objective is undefined
--   - encoding: online: nothing is known about job i until its arrival time a_i → OnlineAlg.causal: if J_{≤t} = J'_{≤t}, the work on each job of J_{≤t} by every time s ≤ t agrees; reason: the weakest form of online-ness, which makes the class of online algorithms as large as possible
--   - generalization: a given finite family of instances J ∈ 𝒥 → any set 𝒥 of valid instances; reason: the finite family is a special case
--   - generalization: the max-min and lexicographic objectives → any positive per-job benchmark b_J(j), with ratio min_j f_j / b_J(j); reason: b_J(j) = f̂_J gives the max-min objective and b_J(j) = f̂_j the lexicographic one (p.3: ratio min_i f_i/f̂_i)
--   - generalization: a schedule runs one job at a time with preemption → schedules are rate schedules; ALG and ALG′ are rate-scheduling online algorithms; reason: the paper's ALG′ itself completes w_i(I) work on each job over each interval 'in arbitrary order', i.e. it is specified by amounts of work, which a rate schedule represents; the hypothesis covers every one-job-at-a-time randomized scheduler
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 6.1, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_OnlineAlg
import Definitions.Def_MaxMinFracSched_RandOnlineAlg

namespace MaxMinFracSched

/-- **Lemma 6.1 (Randomized to deterministic reduction).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 6.1, p.28 (PDF p.30):
"Consider a given finite family of instances J ∈ J. If there exists a randomized scheduler ALG
with expected competitive ratio α on J against any oblivious adversary, then there exists a
deterministic scheduler ALG′ which is α-competitive on J against any online adversary.
Furthermore, this holds for both the max-min and lexicographic objectives."

**Formalization Note.** Stated for any set `𝒥` of valid instances (not only finite ones) and any
positive per-job benchmark `b J j`: if a randomized online algorithm has
`E[min_{j∈J} f_j / b J j] ≥ α` on every `J ∈ 𝒥`, some deterministic online algorithm has
`f_j / b J j ≥ α` for every job of every `J ∈ 𝒥`. With `b J j = f̂_J` this is the max-min
objective; with `b J j = f̂_j` (the lexicographic optimum of job `j`) it is the lexicographic
objective, whose competitive ratio is `min_{i∈J} f_i / f̂_i` (p.3). The deterministic algorithm
is online on every instance. -/
theorem lemma_6_1 {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (A : RandOnlineAlg Ω) (𝒥 : Set (Finset Job))
    (h𝒥 : ∀ J ∈ 𝒥, ValidInstance J) (b : Finset Job → Job → ℝ)
    (hb : ∀ J ∈ 𝒥, ∀ j ∈ J, 0 < b J j) (α : ℝ)
    (hA : ∀ J ∈ 𝒥, α ≤ ∫ ω, (⨅ j : J, frac ((A.alg ω).sched J) (j : Job) / b J (j : Job)) ∂μ) :
    ∃ A' : OnlineAlg, ∀ J ∈ 𝒥, ∀ j ∈ J, α ≤ frac (A'.sched J) j / b J j := by sorry

end MaxMinFracSched
