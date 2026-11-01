-- Prove2me | Theorems.Thm_GreedyReusableNet_eq_12_part_1
-- name    : GreedyReusableNet.eq_12_part_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:26.302102+00:00
-- url     : https://prove2.me/theorems/a59a6a40-d9da-42cc-a242-4479103836bd
-- title:
--   (12), part ① — the good-set part is at most $(\alpha\beta)^{-1}\mathrm{Rew}(\mathrm{GRD}(r))$
-- statement:
--   Assume Assumptions 1, 2, 5.1, 5.2 (and that activated bundles belong to the action taken), and let the oracle be an $(\alpha,\beta)$-oracle with $\alpha,\beta\in(0,1]$. For a threshold $r>0$ run $\mathrm{GRD}(r)$ and an admissible OPT in the queue coupling. Then
--   $$\text{①}=\mathbb E\Big[\sum_t\sum_{B\in\mathcal A^{\mathrm{GRD}(r)}_{t,+}}r\,\mathbb 1\{r_t(B;n^{\mathrm{OPT}}_t(B))\ge r\}\,\mathbb 1^{\mathrm{OPT}}_t\{B\}\Big]\ \le\ (\alpha\beta)^{-1}\,\mathrm{Rew}(\mathrm{GRD}(r)).$$
--   On the good sets the oracle's guarantee lets GRD$(r)$'s expected per-period reward pay for OPT's thresholded reward.
--
--   Differences from the source:
--   - encoding: ① ≤ (αβ)^{-1} Rew(GRD(r)) → αβ · ① ≤ Rew(GRD(r)); reason: multiplied by αβ > 0; the same inequality
--   - generalization: threshold r ∈ [r_min, r_max] → every threshold r > 0; reason: the proof uses only r > 0; [r_min, r_max] ⊂ (0, ∞)
--   - generalization: the benchmark OPT → every admissible policy π′; reason: OPT is an admissible policy; the statement holds for each one
--   - generalization: rewards r_t(B; n) (implicitly nonnegative) → real rewards with no sign condition; reason: the paper states no sign condition; nonnegative rewards are a special case
--   - reading: Assumption 4: the oracle solves max over 𝒜_t up to ratio α with probability at least β → IsApproxOracle: for every t < T, f ≥ 0, n and set of free arms, with probability ≥ β over a uniform seed the output is an available set of 𝒜_t with objective ≥ α times that of every available set of 𝒜_t; the oracle is measurable in its seed; reason: Algorithms 2–4 call the oracle over the available sets; a paper oracle yields one (zero the weights of unavailable bundles, delete them: Assumptions 1, 2); an algorithm's output is a measurable function of its random bits
--   - encoding: the activation draw 'samples an 𝒜^π_{t,act} ⊂ 𝒜^π_t' from a distribution determined by (t, 𝒜^π_t, n^π_t), with marginal ℙ_t (1) → the instance supplies the activation law act A n per period; ℙ_t is defined as its marginal; ActivatesWithinAction states that its support consists of subsets of A for A ∈ 𝒜_t; reason: the model of p.9 written as data; ℙ_t must be the marginal of the law the process samples from
--   - encoding: r_t(B; n(B)) and ℙ_t(B | A, n(B)) depend on n(B) = (n_i)_{i∈B} → reward and activation law take the whole counting vector n; Assumptions 5.1/5.2 compare n, n′ on the coordinates in B only; reason: applied to n, n′ that agree on B, 5.1/5.2 force dependence on n(B) only
--   - encoding: periods t = 1, …, T → periods t = 0, …, T − 1 (t < T); reason: Lean indexing; the same periods shifted by one
--   - encoding: online policies, randomizing over available action sets adapted to the available information → Rule: an initial seed s ∼ seedLaw and a per-period uniform seed; proposals that are not available sets of 𝒜_t are replaced by ∅; IsAdmissible = seedLaw a probability measure and the proposal measurable in the seeds; reason: a seed can encode any randomization; measurability makes the expectation of a randomized policy meaningful; GRD-R's random threshold is its initial seed
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, proof of Theorem 2, part ① of (12), p.41

import Mathlib
import Definitions.Def_GreedyReusableNet_IndepSystemAssumption
import Definitions.Def_GreedyReusableNet_ActivatesWithinAction
import Definitions.Def_GreedyReusableNet_Substitutability
import Definitions.Def_GreedyReusableNet_DecayingReward
import Definitions.Def_GreedyReusableNet_DecayingProbability
import Definitions.Def_GreedyReusableNet_IsApproxOracle
import Definitions.Def_GreedyReusableNet_IsAdmissible
import Definitions.Def_GreedyReusableNet_Rew
import Definitions.Def_GreedyReusableNet_GRD
import Definitions.Def_GreedyReusableNet_coupledRun
import Definitions.Def_GreedyReusableNet_goodSet

open MeasureTheory

namespace GreedyReusableNet

/-- **Proof of Theorem 2, part ① of (12)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, p.41):
"① `= ∑_t 𝔼[∑_{B ∈ 𝒜^{GRD(r)}_{t,+}} r 𝟙{r_t(B; n^OPT_t(B)) ≥ r} 𝟙_t{B}] ≤ ⋯ = (αβ)^{-1} Rew(GRD(r))`."

Run `GRD(r)` (threshold `r > 0` on the total reward) and an admissible OPT `π'` in the queue
coupling. Under Assumptions 1, 2, 5.1, 5.2 and an `(α, β)`-oracle,
`αβ · 𝔼[∑_t ∑_{B activated by OPT at t, B ∈ 𝒜^{GRD(r)}_{t,+}} r 𝟙{r_t(B; n^OPT_t(B)) ≥ r}] ≤ Rew(GRD(r))`.

**Formalization Note** Multiplied by `αβ > 0` instead of the printed `(αβ)^{-1}` on the right.
The paper takes `r ∈ [r_min, r_max]`; the statement holds for every `r > 0`. Periods are 0-based. -/
theorem eq_12_part_1 {N T L : ℕ} (I : ProblemInstance N)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h2 : Substitutability I T) (h51 : DecayingReward I T) (h52 : DecayingProbability I T)
    (α β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (O : Oracle N) (hO : IsApproxOracle I T α β O)
    (r : ℝ) (hr : 0 < r) (π' : Rule N) (hπ' : IsAdmissible π') :
    α * β * ∫ ω, (∑ t ∈ Finset.range T,
        ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
          if B ∈ goodSet (coupledFinal I T (GRD I O r) π' ω).1
                (coupledFinal I T (GRD I O r) π' ω).2.1 t ∧
              r ≤ (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).2.1.take t))
          then r else 0) ∂(coupledLaw T (GRD I O r) π') ≤
      Rew I T (GRD I O r) := by sorry

end GreedyReusableNet
