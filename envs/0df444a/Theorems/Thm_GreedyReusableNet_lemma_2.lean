-- Prove2me | Theorems.Thm_GreedyReusableNet_lemma_2
-- name    : GreedyReusableNet.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:33.817114+00:00
-- url     : https://prove2.me/theorems/2deabc2b-c65a-4306-8295-c8ba68272bfd
-- title:
--   Lemma 2 — OPT's activations outside the good sets are at most π's activated arms
-- statement:
--   Assume Assumptions 1, 3 and 5.3 (and that activated bundles belong to the action taken). Let $\pi$ and OPT be admissible policies run in the queue coupling, and let $\mathcal A^\pi_{t,+}$ be the good sets. Then
--   $$\mathbb E\Big[\sum_t\sum_{B\in\mathcal A^\pi_t}|B|\,\mathbb 1^\pi_t\{B\}\Big]\ \ge\ \mathbb E\Big[\sum_t\sum_{B\in\mathcal A^{\mathrm{OPT}}_t\setminus\mathcal A^\pi_{t,+}}\mathbb 1^{\mathrm{OPT}}_t\{B\}\Big]:$$
--   the expected number of OPT's activations of bundles outside the good sets is at most the expected number of arms $\pi$ activates.
--
--   The bound holds for any two policies; it is the step of the analysis that pays for the bundles OPT could serve but $\pi$ could not, because $\pi$ had blocked or over-used one of their arms.
--
--   Differences from the source:
--   - generalization: the benchmark OPT → every admissible policy π′; reason: OPT is an admissible policy; the statement holds for each one
--   - generalization: blocking times b ∈ ℤ₊₊ with law F_i(·; n), Assumption 5.3 for x ∈ ℤ₊₊ → blocking times in ℕ (b = 0 allowed), Assumption 5.3 for every x ∈ ℕ; reason: p.11 itself allows b = 0 and the paper's examples use F_i(x; n) = 𝟙{x ≥ 0}; a ℤ₊₊-valued law satisfies the x = 0 case trivially, so every instance of the paper is covered
--   - reading: Assumption 3: 𝔼[𝟙^π_t{B₁}𝟙^π_t{B₂}] = 0 for overlapping B₁ ≠ B₂ and any online policy π → every outcome of the activation law act A n (A ∈ 𝒜_t, any n) has pairwise disjoint distinct bundles; reason: p.10 explains Assumption 3 as 'for each random realization of the activation mechanism, any two different activated sets do not have arms in common'
--   - encoding: the activation draw 'samples an 𝒜^π_{t,act} ⊂ 𝒜^π_t' from a distribution determined by (t, 𝒜^π_t, n^π_t), with marginal ℙ_t (1) → the instance supplies the activation law act A n per period; ℙ_t is defined as its marginal; ActivatesWithinAction states that its support consists of subsets of A for A ∈ 𝒜_t; reason: the model of p.9 written as data; ℙ_t must be the marginal of the law the process samples from
--   - encoding: periods t = 1, …, T → periods t = 0, …, T − 1 (t < T); reason: Lean indexing; the same periods shifted by one
--   - encoding: online policies, randomizing over available action sets adapted to the available information → Rule: an initial seed s ∼ seedLaw and a per-period uniform seed; proposals that are not available sets of 𝒜_t are replaced by ∅; IsAdmissible = seedLaw a probability measure and the proposal measurable in the seeds; reason: a seed can encode any randomization; measurability makes the expectation of a randomized policy meaningful; GRD-R's random threshold is its initial seed
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.2, Lemma 2, p.21 (proof pp.38–39)

import Mathlib
import Definitions.Def_GreedyReusableNet_IndepSystemAssumption
import Definitions.Def_GreedyReusableNet_ActivatesWithinAction
import Definitions.Def_GreedyReusableNet_NonOverlappingActivation
import Definitions.Def_GreedyReusableNet_DecayingAvailability
import Definitions.Def_GreedyReusableNet_IsAdmissible
import Definitions.Def_GreedyReusableNet_coupledRun
import Definitions.Def_GreedyReusableNet_goodSet

open MeasureTheory

namespace GreedyReusableNet

/-- **Lemma 2** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §3.2, p.21; proof pp.38–39): "Suppose
Assumption 1, 3, 5.3 hold. Then for any online policy `π`, we have
`𝔼[∑_t ∑_{B ∈ 𝒜^π_t} |B| 𝟙^π_t{B}] ≥ 𝔼[∑_t ∑_{B ∈ 𝒜^OPT_t \ 𝒜^π_{t,+}} 𝟙^OPT_t{B}]`."

For admissible policies `π` and OPT `π'` in the queue coupling, under Assumptions 1, 3 and 5.3:
the expected number of OPT's activated bundles outside the good sets `𝒜^π_{t,+}` (`goodSet`) is
at most the expected number of arms `π` activates, `∑_t ∑_{B activated by π} |B|`.

**Formalization Note** Periods `t < T` are 0-based. OPT's activated bundles lie in its action
set, so summing over OPT's activated bundles not in `goodSet` is the paper's sum over
`𝒜^OPT_t \ 𝒜^π_{t,+}` weighted by `𝟙^OPT_t{B}`. -/
theorem lemma_2 {N T L : ℕ} (I : ProblemInstance N)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h3 : NonOverlappingActivation I T) (h53 : DecayingAvailability I)
    (π π' : Rule N) (hπ : IsAdmissible π) (hπ' : IsAdmissible π') :
    ∫ ω, (∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T π π' ω).2.1 t,
        if B ∈ goodSet (coupledFinal I T π π' ω).1 (coupledFinal I T π π' ω).2.1 t
        then (0 : ℝ) else 1) ∂(coupledLaw T π π') ≤
      ∫ ω, (∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T π π' ω).1 t,
        (B.card : ℝ)) ∂(coupledLaw T π π') := by sorry

end GreedyReusableNet
