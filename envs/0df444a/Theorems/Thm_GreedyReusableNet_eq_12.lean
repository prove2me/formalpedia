-- Prove2me | Theorems.Thm_GreedyReusableNet_eq_12
-- name    : GreedyReusableNet.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:37:58.939303+00:00
-- url     : https://prove2.me/theorems/3143b25c-27d1-4ed5-a5d2-0b8f3f9d5a83
-- title:
--   (12) — $\mathrm{Rew}(\mathrm{GRD}(r))\ge\frac{\alpha\beta}{1+\alpha\beta L}\mathbb E[\sum r\mathbb 1\{r_t\ge r\}\mathbb 1^{\mathrm{OPT}}]$
-- statement:
--   Assume Assumptions 1 (with bundle sizes at most $L$), 2, 3, 5.1, 5.2, 5.3 (and that activated bundles belong to the action taken), and let the oracle be an $(\alpha,\beta)$-oracle with $\alpha,\beta\in(0,1]$. For every threshold $r>0$ and every admissible policy OPT,
--   $$\mathrm{Rew}(\mathrm{GRD}(r))\ \ge\ \frac{\alpha\beta}{1+\alpha\beta L}\,\mathbb E\Big[\sum_t\sum_{B\in\mathcal A^{\mathrm{OPT}}_t}r\,\mathbb 1\{r_t(B;n^{\mathrm{OPT}}_t(B))\ge r\}\,\mathbb 1^{\mathrm{OPT}}_t\{B\}\Big],$$
--   the expectation on the right over OPT's own run. This is (12) of the proof of Theorem 2: the greedy policy with a fixed threshold competes with the part of OPT's reward that lies above the threshold, each such activation counted as $r$.
--
--   Differences from the source:
--   - reading: the left side of (12) is written 'GRD(r)' → Rew(GRD(r)); reason: the policy's total expected reward, as in (5)–(6)
--   - generalization: threshold r ∈ [r_min, r_max] → every threshold r > 0; reason: the proof uses only r > 0; [r_min, r_max] ⊂ (0, ∞)
--   - generalization: the benchmark OPT → every admissible policy π′; reason: OPT is an admissible policy; the statement holds for each one
--   - generalization: rewards r_t(B; n) (implicitly nonnegative) → real rewards with no sign condition; reason: the paper states no sign condition; nonnegative rewards are a special case
--   - generalization: blocking times b ∈ ℤ₊₊ with law F_i(·; n), Assumption 5.3 for x ∈ ℤ₊₊ → blocking times in ℕ (b = 0 allowed), Assumption 5.3 for every x ∈ ℕ; reason: p.11 itself allows b = 0 and the paper's examples use F_i(x; n) = 𝟙{x ≥ 0}; a ℤ₊₊-valued law satisfies the x = 0 case trivially, so every instance of the paper is covered
--   - reading: Assumption 4: the oracle solves max over 𝒜_t up to ratio α with probability at least β → IsApproxOracle: for every t < T, f ≥ 0, n and set of free arms, with probability ≥ β over a uniform seed the output is an available set of 𝒜_t with objective ≥ α times that of every available set of 𝒜_t; the oracle is measurable in its seed; reason: Algorithms 2–4 call the oracle over the available sets; a paper oracle yields one (zero the weights of unavailable bundles, delete them: Assumptions 1, 2); an algorithm's output is a measurable function of its random bits
--   - reading: Assumption 3: 𝔼[𝟙^π_t{B₁}𝟙^π_t{B₂}] = 0 for overlapping B₁ ≠ B₂ and any online policy π → every outcome of the activation law act A n (A ∈ 𝒜_t, any n) has pairwise disjoint distinct bundles; reason: p.10 explains Assumption 3 as 'for each random realization of the activation mechanism, any two different activated sets do not have arms in common'
--   - encoding: the activation draw 'samples an 𝒜^π_{t,act} ⊂ 𝒜^π_t' from a distribution determined by (t, 𝒜^π_t, n^π_t), with marginal ℙ_t (1) → the instance supplies the activation law act A n per period; ℙ_t is defined as its marginal; ActivatesWithinAction states that its support consists of subsets of A for A ∈ 𝒜_t; reason: the model of p.9 written as data; ℙ_t must be the marginal of the law the process samples from
--   - encoding: r_t(B; n(B)) and ℙ_t(B | A, n(B)) depend on n(B) = (n_i)_{i∈B} → reward and activation law take the whole counting vector n; Assumptions 5.1/5.2 compare n, n′ on the coordinates in B only; reason: applied to n, n′ that agree on B, 5.1/5.2 force dependence on n(B) only
--   - encoding: periods t = 1, …, T → periods t = 0, …, T − 1 (t < T); reason: Lean indexing; the same periods shifted by one
--   - encoding: online policies, randomizing over available action sets adapted to the available information → Rule: an initial seed s ∼ seedLaw and a per-period uniform seed; proposals that are not available sets of 𝒜_t are replaced by ∅; IsAdmissible = seedLaw a probability measure and the proposal measurable in the seeds; reason: a seed can encode any randomization; measurability makes the expectation of a randomized policy meaningful; GRD-R's random threshold is its initial seed
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, proof of Theorem 2, eq. (12), p.40

import Mathlib
import Definitions.Def_GreedyReusableNet_IndepSystemAssumption
import Definitions.Def_GreedyReusableNet_ActivatesWithinAction
import Definitions.Def_GreedyReusableNet_Substitutability
import Definitions.Def_GreedyReusableNet_NonOverlappingActivation
import Definitions.Def_GreedyReusableNet_DecayingReward
import Definitions.Def_GreedyReusableNet_DecayingProbability
import Definitions.Def_GreedyReusableNet_DecayingAvailability
import Definitions.Def_GreedyReusableNet_IsApproxOracle
import Definitions.Def_GreedyReusableNet_IsAdmissible
import Definitions.Def_GreedyReusableNet_Rew
import Definitions.Def_GreedyReusableNet_GRD

open MeasureTheory

namespace GreedyReusableNet

/-- **(12)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, proof of Theorem 2, p.40): "Let `GRD(r)` be
the greedy policy when the random threshold for total reward is `r`. We prove the following:
`GRD(r) ≥ αβ/(1 + αβL) 𝔼[∑_t ∑_{B ∈ 𝒜^OPT_t} r 𝟙{r_t(B; n^OPT_t(B)) ≥ r} 𝟙^OPT_t{B}]`."

Under Assumptions 1 (bundle size bound `L`), 2, 3, 5 and an `(α, β)`-oracle, for every threshold
`r > 0` and every admissible policy OPT `π'`:
`Rew(GRD(r)) ≥ αβ/(1 + αβL) · 𝔼_{π'}[∑_t ∑_{B activated at t} r 𝟙{r_t(B; n_t(B)) ≥ r}]`, the
expectation over OPT's own run.

**Formalization Note** "`GRD(r)`" on the left of (12) is its total expected reward
`Rew(GRD(r))`. The paper takes `r ∈ [r_min, r_max]`; the statement holds for every `r > 0`. -/
theorem eq_12 {N T L : ℕ} (I : ProblemInstance N)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h2 : Substitutability I T) (h3 : NonOverlappingActivation I T)
    (h51 : DecayingReward I T) (h52 : DecayingProbability I T) (h53 : DecayingAvailability I)
    (α β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (O : Oracle N) (hO : IsApproxOracle I T α β O)
    (r : ℝ) (hr : 0 < r) (π' : Rule N) (hπ' : IsAdmissible π') :
    α * β / (1 + α * β * L) *
        expectedSum I T π' (fun t B n => if r ≤ (I.period t).reward B n then r else 0) ≤
      Rew I T (GRD I O r) := by sorry

end GreedyReusableNet
