-- Prove2me | Theorems.Thm_GreedyReusableNet_eq_12_part_2
-- name    : GreedyReusableNet.eq_12_part_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:13.960922+00:00
-- url     : https://prove2.me/theorems/b6e0fd5f-7d27-428e-9f92-2faa86aabe6e
-- title:
--   (12), part ② — the part outside the good sets is at most $L\cdot\mathrm{Rew}(\mathrm{GRD}(r))$
-- statement:
--   Assume Assumptions 1 (with bundle sizes at most $L$), 3 and 5.3 (and that activated bundles belong to the action taken). For a threshold $r>0$ and any oracle, run $\mathrm{GRD}(r)$ and an admissible OPT in the queue coupling. Then
--   $$\text{②}=\mathbb E\Big[\sum_t\sum_{B\in\mathcal A^{\mathrm{OPT}}_t\setminus\mathcal A^{\mathrm{GRD}(r)}_{t,+}}r\,\mathbb 1\{r_t(B;n^{\mathrm{OPT}}_t(B))\ge r\}\,\mathbb 1^{\mathrm{OPT}}_t\{B\}\Big]\ \le\ L\cdot\mathrm{Rew}(\mathrm{GRD}(r)).$$
--   Through Corollary 1, OPT's activations outside the good sets are charged to GRD$(r)$'s activations, each of which earns at least $r$.
--
--   Differences from the source:
--   - generalization: threshold r ∈ [r_min, r_max] → every threshold r > 0; reason: the proof uses only r > 0; [r_min, r_max] ⊂ (0, ∞)
--   - generalization: the benchmark OPT → every admissible policy π′; reason: OPT is an admissible policy; the statement holds for each one
--   - generalization: rewards r_t(B; n) (implicitly nonnegative) → real rewards with no sign condition; reason: the paper states no sign condition; nonnegative rewards are a special case
--   - generalization: blocking times b ∈ ℤ₊₊ with law F_i(·; n), Assumption 5.3 for x ∈ ℤ₊₊ → blocking times in ℕ (b = 0 allowed), Assumption 5.3 for every x ∈ ℕ; reason: p.11 itself allows b = 0 and the paper's examples use F_i(x; n) = 𝟙{x ≥ 0}; a ℤ₊₊-valued law satisfies the x = 0 case trivially, so every instance of the paper is covered
--   - reading: Assumption 3: 𝔼[𝟙^π_t{B₁}𝟙^π_t{B₂}] = 0 for overlapping B₁ ≠ B₂ and any online policy π → every outcome of the activation law act A n (A ∈ 𝒜_t, any n) has pairwise disjoint distinct bundles; reason: p.10 explains Assumption 3 as 'for each random realization of the activation mechanism, any two different activated sets do not have arms in common'
--   - encoding: the activation draw 'samples an 𝒜^π_{t,act} ⊂ 𝒜^π_t' from a distribution determined by (t, 𝒜^π_t, n^π_t), with marginal ℙ_t (1) → the instance supplies the activation law act A n per period; ℙ_t is defined as its marginal; ActivatesWithinAction states that its support consists of subsets of A for A ∈ 𝒜_t; reason: the model of p.9 written as data; ℙ_t must be the marginal of the law the process samples from
--   - encoding: periods t = 1, …, T → periods t = 0, …, T − 1 (t < T); reason: Lean indexing; the same periods shifted by one
--   - encoding: online policies, randomizing over available action sets adapted to the available information → Rule: an initial seed s ∼ seedLaw and a per-period uniform seed; proposals that are not available sets of 𝒜_t are replaced by ∅; IsAdmissible = seedLaw a probability measure and the proposal measurable in the seeds; reason: a seed can encode any randomization; measurability makes the expectation of a randomized policy meaningful; GRD-R's random threshold is its initial seed
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, proof of Theorem 2, part ② of (12), pp.41–42

import Mathlib
import Definitions.Def_GreedyReusableNet_IndepSystemAssumption
import Definitions.Def_GreedyReusableNet_ActivatesWithinAction
import Definitions.Def_GreedyReusableNet_NonOverlappingActivation
import Definitions.Def_GreedyReusableNet_DecayingAvailability
import Definitions.Def_GreedyReusableNet_IsAdmissible
import Definitions.Def_GreedyReusableNet_Rew
import Definitions.Def_GreedyReusableNet_GRD
import Definitions.Def_GreedyReusableNet_coupledRun
import Definitions.Def_GreedyReusableNet_goodSet

open MeasureTheory

namespace GreedyReusableNet

/-- **Proof of Theorem 2, part ② of (12)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, pp.41–42):
"For ②, by taking `π = GRD(r)`, we have
② `= 𝔼[∑_t ∑_{B ∈ 𝒜^OPT_t \ 𝒜^{GRD(r)}_{t,+}} r 𝟙{r_t(B; n^OPT_t(B)) ≥ r} 𝟙^OPT_t{B}] ≤ ⋯ ≤ L · Rew(GRD(r))`."

Run `GRD(r)` (threshold `r > 0`, any oracle) and an admissible OPT `π'` in the queue coupling.
Under Assumptions 1 (bundle size bound `L`), 3 and 5.3,
`𝔼[∑_t ∑_{B activated by OPT at t, B ∉ 𝒜^{GRD(r)}_{t,+}} r 𝟙{r_t(B; n^OPT_t(B)) ≥ r}] ≤ L · Rew(GRD(r))`.

**Formalization Note** The paper takes `r ∈ [r_min, r_max]`; the statement holds for every
`r > 0`. Periods are 0-based. -/
theorem eq_12_part_2 {N T L : ℕ} (I : ProblemInstance N)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h3 : NonOverlappingActivation I T) (h53 : DecayingAvailability I)
    (O : Oracle N) (r : ℝ) (hr : 0 < r) (π' : Rule N) (hπ' : IsAdmissible π') :
    ∫ ω, (∑ t ∈ Finset.range T,
        ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
          if B ∉ goodSet (coupledFinal I T (GRD I O r) π' ω).1
                (coupledFinal I T (GRD I O r) π' ω).2.1 t ∧
              r ≤ (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).2.1.take t))
          then r else 0) ∂(coupledLaw T (GRD I O r) π') ≤
      (L : ℝ) * Rew I T (GRD I O r) := by sorry

end GreedyReusableNet
