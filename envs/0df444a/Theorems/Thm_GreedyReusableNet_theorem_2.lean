-- Prove2me | Theorems.Thm_GreedyReusableNet_theorem_2
-- name    : GreedyReusableNet.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:29.418982+00:00
-- url     : https://prove2.me/theorems/e8a3bec1-27f1-4468-952a-bceb05f6cf3d
-- title:
--   Theorem 2 — GRD-R and $\overline{\mathrm{GRD}}$-R are $\frac{\alpha\beta}{(1+\alpha\beta L)(1+\ln R)}$- and $\frac{\alpha\beta}{(1+\alpha\beta L)(1+\ln\bar R)}$-competitive
-- statement:
--   Consider the online matching problem with reusable network resources and decaying rewards: in each period $t=1,\dots,T$ a basis $\mathcal B_t$ of bundles of arms, an independence system $\mathscr A_t$ of action sets, an activation law and rewards $r_t(B;n(B))$ are revealed; a policy takes an available action set; the activated bundles pay their rewards, and each activated arm $i$ is blocked for a random time drawn from $F_i(\cdot\,;n_i)$, where $n_i$ counts its earlier activations.
--
--   Assume Assumptions 1 (bundles of at most $L$ arms), 2, 3 and 5 (activated bundles belong to the action taken), and let the oracle be an $(\alpha,\beta)$-oracle, $\alpha,\beta\in(0,1]$. Then for every horizon $T$:
--
--   1. **(5)** If $0<r_{\min}\le r_{\max}$ with $r_t(B;n)\le r_{\max}$ for all $t$, $B\in\mathcal B_t$, $n$, and $r_t(B;n)\ge r_{\min}$ whenever $r_t(B;n)>0$, then, with $R=r_{\max}/r_{\min}$, every admissible policy OPT satisfies
--   $$\frac{\alpha\beta}{(1+\alpha\beta L)(1+\ln R)}\,\mathrm{Rew}(\mathrm{OPT})\ \le\ \mathrm{Rew}(\mathrm{GRD\text{-}R}).$$
--   2. **(6)** If every bundle is nonempty and $0<\bar r_{\min}\le\bar r_{\max}$ bound the average rewards $\bar r_t(B;n)=r_t(B;n)/|B|$ in the same way, then, with $\bar R=\bar r_{\max}/\bar r_{\min}$,
--   $$\frac{\alpha\beta}{(1+\alpha\beta L)(1+\ln\bar R)}\,\mathrm{Rew}(\mathrm{OPT})\ \le\ \mathrm{Rew}(\overline{\mathrm{GRD}}\text{-R}).$$
--
--   Equivalently $\mathrm{Rew}(\mathrm{GRD\text{-}R})/\mathrm{Rew}(\mathrm{OPT})\ge\alpha\beta/((1+\alpha\beta L)(1+\ln R))$, where $\mathrm{Rew}(\mathrm{OPT})$ is the best expected reward of a policy that knows the whole instance in advance but not the realizations. A random threshold drawn once from a log-type law reduces the linear dependence on the reward ratio of the plain greedy policy to a logarithmic one.
--
--   Differences from the source:
--   - encoding: Rew(GRD-R)/Rew(OPT) ≥ c, OPT the clairvoyant optimal policy → c · Rew(π′) ≤ Rew(GRD-R) for every admissible policy π′; reason: Rew(OPT) is the supremum over admissible policies; the multiplied form is equivalent and avoids 0/0 and attainment of the supremum
--   - reading: (6) for every instance → (6) under the hypothesis that every bundle of 𝓑_t (t < T) is nonempty; reason: r̄_t(B; n) = r_t(B; n)/|B| is undefined for B = ∅, so the bounds r̄_min, r̄_max presuppose nonempty bundles; with Lean's x/0 = 0 an empty bundle of positive reward would be invisible to GRD̄-R and (6) false (T = 1, 𝓑 = {∅}, 𝒜 = {∅, {∅}}); (5) needs no such hypothesis
--   - reading: positive numbers r_max ≥ sup r_t ≥ inf{r_t | r_t > 0} ≥ r_min (sup/inf over t, B ∈ 𝓑_t, n) → 0 < r_min ≤ r_max, r_t(B; n) ≤ r_max, and r_t(B; n) > 0 → r_t(B; n) ≥ r_min, for all t < T, B ∈ 𝓑_t, n (same for r̄); reason: the printed chain of inequalities; r_min ≤ r_max makes G a distribution function
--   - generalization: L ∈ ℤ₊ and ∀ T ≥ 1 → any L : ℕ and any T : ℕ; reason: L = 0 forces empty bundles and T = 0 makes both sides 0; the printed range is a special case
--   - generalization: rewards r_t(B; n) (implicitly nonnegative) → real rewards with no sign condition; reason: the paper states no sign condition; nonnegative rewards are a special case
--   - generalization: blocking times b ∈ ℤ₊₊ with law F_i(·; n), Assumption 5.3 for x ∈ ℤ₊₊ → blocking times in ℕ (b = 0 allowed), Assumption 5.3 for every x ∈ ℕ; reason: p.11 itself allows b = 0 and the paper's examples use F_i(x; n) = 𝟙{x ≥ 0}; a ℤ₊₊-valued law satisfies the x = 0 case trivially, so every instance of the paper is covered
--   - reading: Assumption 4: the oracle solves max over 𝒜_t up to ratio α with probability at least β → IsApproxOracle: for every t < T, f ≥ 0, n and set of free arms, with probability ≥ β over a uniform seed the output is an available set of 𝒜_t with objective ≥ α times that of every available set of 𝒜_t; the oracle is measurable in its seed; reason: Algorithms 2–4 call the oracle over the available sets; a paper oracle yields one (zero the weights of unavailable bundles, delete them: Assumptions 1, 2); an algorithm's output is a measurable function of its random bits
--   - reading: Assumption 3: 𝔼[𝟙^π_t{B₁}𝟙^π_t{B₂}] = 0 for overlapping B₁ ≠ B₂ and any online policy π → every outcome of the activation law act A n (A ∈ 𝒜_t, any n) has pairwise disjoint distinct bundles; reason: p.10 explains Assumption 3 as 'for each random realization of the activation mechanism, any two different activated sets do not have arms in common'
--   - encoding: the activation draw 'samples an 𝒜^π_{t,act} ⊂ 𝒜^π_t' from a distribution determined by (t, 𝒜^π_t, n^π_t), with marginal ℙ_t (1) → the instance supplies the activation law act A n per period; ℙ_t is defined as its marginal; ActivatesWithinAction states that its support consists of subsets of A for A ∈ 𝒜_t; reason: the model of p.9 written as data; ℙ_t must be the marginal of the law the process samples from
--   - encoding: r_t(B; n(B)) and ℙ_t(B | A, n(B)) depend on n(B) = (n_i)_{i∈B} → reward and activation law take the whole counting vector n; Assumptions 5.1/5.2 compare n, n′ on the coordinates in B only; reason: applied to n, n′ that agree on B, 5.1/5.2 force dependence on n(B) only
--   - encoding: the law with distribution function G(x) = (1 + ln(x/r_min))/(1 + ln R) on [r_min, r_max] → thresholdLaw a b = atom 1/(1 + ln(b/a)) at a plus density 1/((1 + ln(b/a)) x) on (a, b]; reason: the same law: the verification file proves it is a probability measure with distribution function G on [a, b]
--   - encoding: periods t = 1, …, T → periods t = 0, …, T − 1 (t < T); reason: Lean indexing; the same periods shifted by one
--   - encoding: online policies, randomizing over available action sets adapted to the available information → Rule: an initial seed s ∼ seedLaw and a per-period uniform seed; proposals that are not available sets of 𝒜_t are replaced by ∅; IsAdmissible = seedLaw a probability measure and the proposal measurable in the seeds; reason: a seed can encode any randomization; measurability makes the expectation of a randomized policy meaningful; GRD-R's random threshold is its initial seed
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.1, Theorem 2, eqs. (5)–(6), p.18 (proof pp.40–44)

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
import Definitions.Def_GreedyReusableNet_avgReward
import Definitions.Def_GreedyReusableNet_GRD_R
import Definitions.Def_GreedyReusableNet_GRDbar_R

open MeasureTheory

namespace GreedyReusableNet

/-- **Theorem 2** (Simchi-Levi, Zheng & Zhu, *On Greedy-like Policies in Online Matching with
Reusable Network Resources and Decaying Rewards*, SSRN 3981123, §3.1, p.18): "Under Assumptions
1, 2, 3, 4, 5, `∀T ≥ 1`, GRD-R and GRD̄-R has the following theoretical guarantee:
`Rew(GRD-R)/Rew(OPT) ≥ αβ/((1 + αβL)(1 + ln R))`, (5)
`Rew(GRD̄-R)/Rew(OPT) ≥ αβ/((1 + αβL)(1 + ln R̄))`. (6)"

For every horizon `T`, every instance satisfying Assumptions 1 (bundle size bound `L`), 2, 3,
5.1, 5.2, 5.3 (and the model condition that activated bundles belong to the action taken), every
`α, β ∈ (0, 1]` and every `(α, β)`-oracle:

1. **(5)** for all `0 < r_min ≤ r_max` with `r_t(B; n) ≤ r_max` for every `t < T`, `B ∈ 𝓑_t`, `n`,
   and `r_t(B; n) ≥ r_min` whenever `r_t(B; n) > 0`: every admissible policy `π'` satisfies
   `αβ/((1 + αβL)(1 + ln(r_max/r_min))) · Rew(π') ≤ Rew(GRD-R)`;
2. **(6)** if every bundle is nonempty, the same with GRD̄-R and bounds `0 < r̄_min ≤ r̄_max` on
   the average reward per arm `r̄_t(B; n) = r_t(B; n)/|B|`.

**Formalization Note** `Rew(OPT)` is the supremum of `Rew(π')` over all admissible policies
(the clairvoyant optimum knows the instance but not the future randomness, p.15), so the ratio
bounds are stated as `c · Rew(π') ≤ Rew(GRD-R)` for every admissible `π'`. Periods are 0-based,
blocking times are in `ℕ`, rewards carry no sign condition. Nonempty bundles are assumed in (6)
only because `r̄` is undefined for the empty bundle. -/
theorem theorem_2 {N T L : ℕ} (I : ProblemInstance N)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h2 : Substitutability I T) (h3 : NonOverlappingActivation I T)
    (h51 : DecayingReward I T) (h52 : DecayingProbability I T) (h53 : DecayingAvailability I)
    (α β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (O : Oracle N) (hO : IsApproxOracle I T α β O) :
    (∀ rmin rmax : ℝ, 0 < rmin → rmin ≤ rmax →
      (∀ t < T, ∀ B ∈ (I.period t).bundles, ∀ n : Fin N → ℕ,
        (I.period t).reward B n ≤ rmax) →
      (∀ t < T, ∀ B ∈ (I.period t).bundles, ∀ n : Fin N → ℕ,
        0 < (I.period t).reward B n → rmin ≤ (I.period t).reward B n) →
      ∀ π' : Rule N, IsAdmissible π' →
        α * β / ((1 + α * β * L) * (1 + Real.log (rmax / rmin))) * Rew I T π' ≤
          Rew I T (GRD_R I O rmin rmax)) ∧
    ((∀ t < T, ∀ B ∈ (I.period t).bundles, B.Nonempty) →
      ∀ rbmin rbmax : ℝ, 0 < rbmin → rbmin ≤ rbmax →
      (∀ t < T, ∀ B ∈ (I.period t).bundles, ∀ n : Fin N → ℕ,
        avgReward (I.period t) B n ≤ rbmax) →
      (∀ t < T, ∀ B ∈ (I.period t).bundles, ∀ n : Fin N → ℕ,
        0 < avgReward (I.period t) B n → rbmin ≤ avgReward (I.period t) B n) →
      ∀ π' : Rule N, IsAdmissible π' →
        α * β / ((1 + α * β * L) * (1 + Real.log (rbmax / rbmin))) * Rew I T π' ≤
          Rew I T (GRDbar_R I O rbmin rbmax)) := by sorry

end GreedyReusableNet
