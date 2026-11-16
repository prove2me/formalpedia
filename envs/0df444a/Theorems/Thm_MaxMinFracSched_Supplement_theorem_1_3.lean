-- Prove2me | Theorems.Thm_MaxMinFracSched_Supplement_theorem_1_3
-- name    : MaxMinFracSched.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:25:54.386572+00:00
-- url     : https://prove2.me/theorems/36e46c4a-3a5d-4cbf-954b-663de064a0e7
-- title:
--   Theorem 1.3 — no online algorithm, even randomized against an oblivious adversary, has a constant positive ratio for the lexicographic objective
-- statement:
--   For the lexicographic objective the offline benchmark of job $i$ is its fraction $\hat f_{J,i}$ in a lexicographically optimal schedule of $J$: one whose nondecreasingly sorted vector of fractional completions is lexicographically largest. An online algorithm is measured by $\min_{i\in J} f_i/\hat f_{J,i}$, and a randomized one by the expectation of this minimum.
--
--   **Theorem.** For every randomized online algorithm $A$ (on any probability space, with the instance fixed before the random outcome is drawn, i.e. against an oblivious adversary) and every $\alpha>0$, there is a valid instance $J$ that has a lexicographically optimal schedule and such that for every lexicographically optimal schedule $r$ of $J$
--   $$
--   \mathbb E_{\omega}\Bigl[\min_{j\in J}\frac{f_j(A_\omega)}{f_j(r)}\Bigr]<\alpha .
--   $$
--   Deterministic algorithms are the case of a one-point distribution.
--
--   Unlike the max-min objective, where ScaledEDF$(1/2)$ is $1/2$-competitive, the lexicographic objective admits no online algorithm with any constant positive ratio.
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: the base mission's published convention; labels only allow repeated triples
--   - generalization: a schedule runs one job at a time with preemption → online algorithms produce rate schedules (OnlineAlg, RandOnlineAlg); reason: every one-job-at-a-time algorithm is a rate algorithm, so the impossibility over rate algorithms contains the source's
--   - encoding: f̂_i, the job's fraction in the lexicographic optimum → frac r j for a lexicographically optimal rate schedule r; the conclusion holds for every such r, and existence is asserted; reason: the lexicographic optimum over rate schedules is the paper's (its bounds use only interval capacities); every lex-optimal r gives the same vector (Corollary 7.4)
--   - encoding: a randomized scheduler against an oblivious adversary → RandOnlineAlg Ω: a family of OnlineAlg indexed by ω with rates jointly measurable in (ω, t); the instance is chosen before ω; reason: the base mission's convention; joint measurability only excludes schedulers whose expected objective is undefined
--   - encoding: no online algorithm achieves any constant non-zero competitive ratio → for every α > 0 some valid instance has E[min_j f_j / f̂_{J,j}] < α; reason: the negation of "some α > 0 has E[min_j f_j/f̂_j] ≥ α on every instance"
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 1.3, p.4 (PDF p.6); restated and proved p.39 (PDF p.41); objective p.3 (PDF p.5) and p.33 (PDF p.35)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_OnlineAlg
import Definitions.Def_MaxMinFracSched_RandOnlineAlg
import Definitions.Def_MaxMinFracSched_Supplement_IsLexOpt

namespace MaxMinFracSched

namespace Supplement

/-- **Theorem 1.3 (no constant ratio for the lexicographic objective).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 1.3, p.4 (PDF p.6; restated and proved p.39, PDF p.41): "There is no online
algorithm (deterministic or randomized, even against an oblivious adversary), that achieves any
constant non-zero competitive ratio for the lexicographic objective of the max-min fractional
scheduling problem." The ratio is `min_{i∈J} f_i / f̂_i` (p.3, p.33), its expectation for a
randomized algorithm.

For every randomized online algorithm (on any probability space; the instance is fixed before the
randomness, which is the oblivious adversary) and every `α > 0` there is a valid instance `J` that
has a lexicographically optimal schedule and such that for every lexicographically optimal
schedule `r` of `J`, `E[min_{j∈J} f_j / f̂_{J,j}] < α`, where `f̂_{J,j} = frac r j`.

**Formalization Note.** Deterministic algorithms are the case of a Dirac measure. The integrand is
measurable (joint measurability of the algorithm) and bounded (each `f̂_{J,j}` is positive for a
valid instance), so the expectation is a genuine one. -/
theorem theorem_1_3 :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (A : RandOnlineAlg Ω) (α : ℝ), 0 < α →
      ∃ J, ValidInstance J ∧ (∃ r, IsLexOpt J r) ∧
        ∀ r, IsLexOpt J r →
          ∫ ω, (⨅ j : J, frac ((A.alg ω).sched J) (j : Job) / frac r (j : Job)) ∂μ < α := by sorry

end Supplement

end MaxMinFracSched
