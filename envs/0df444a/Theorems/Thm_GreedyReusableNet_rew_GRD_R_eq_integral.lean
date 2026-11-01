-- Prove2me | Theorems.Thm_GreedyReusableNet_rew_GRD_R_eq_integral
-- name    : GreedyReusableNet.rew_GRD_R_eq_integral
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:22.79261+00:00
-- url     : https://prove2.me/theorems/0fc02665-3530-4643-a467-1e0054bf0466
-- title:
--   p.42–43 — $\mathrm{Rew}(\mathrm{GRD\text{-}R})=\mathbb E_r[\mathrm{Rew}(\mathrm{GRD}(r))]$ and its $\overline{\mathrm{GRD}}$ analogue
-- statement:
--   For $0<a\le b$ and any oracle, the expected reward of GRD-R, whose threshold is drawn from the law $G$ on $[a,b]$ inside the run, is the $G$-average of the expected rewards of the fixed-threshold policies:
--   $$\mathrm{Rew}(\mathrm{GRD\text{-}R})=\int\mathrm{Rew}(\mathrm{GRD}(r))\,dG(r),\qquad \mathrm{Rew}(\overline{\mathrm{GRD}}\text{-R})=\int\mathrm{Rew}(\overline{\mathrm{GRD}}(\bar r))\,dG(\bar r).$$
--   These are the first lines of the final chains of the proof of Theorem 2 (p.42 for GRD-R, p.43 for $\overline{\mathrm{GRD}}$-R).
--
--   Differences from the source:
--   - generalization: the (α,β)-oracle of Theorem 2 → any oracle; reason: the identity uses no property of the oracle beyond measurability in its seed
--   - encoding: the law with distribution function G(x) = (1 + ln(x/r_min))/(1 + ln R) on [r_min, r_max] → thresholdLaw a b = atom 1/(1 + ln(b/a)) at a plus density 1/((1 + ln(b/a)) x) on (a, b]; reason: the same law: the verification file proves it is a probability measure with distribution function G on [a, b]
--   - encoding: online policies, randomizing over available action sets adapted to the available information → Rule: an initial seed s ∼ seedLaw and a per-period uniform seed; proposals that are not available sets of 𝒜_t are replaced by ∅; IsAdmissible = seedLaw a probability measure and the proposal measurable in the seeds; reason: a seed can encode any randomization; measurability makes the expectation of a randomized policy meaningful; GRD-R's random threshold is its initial seed
--   - generalization: r ∼ G on [r_min, r_max], where r_min, r_max bound the rewards of an instance satisfying Assumptions 1–5 → any 0 < a ≤ b and any instance, with no bound linking a, b to the rewards and no assumption on the instance; reason: the identity is Fubini over the threshold drawn once before the run; it uses neither the reward bounds nor the assumptions; with a = r_min, b = r_max (resp. r̄_min, r̄_max) it is the printed line
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, proof of Theorem 2, p.42 (first line of the final chain) and p.43

import Mathlib
import Definitions.Def_GreedyReusableNet_Rew
import Definitions.Def_GreedyReusableNet_GRD
import Definitions.Def_GreedyReusableNet_GRDbar
import Definitions.Def_GreedyReusableNet_GRD_R
import Definitions.Def_GreedyReusableNet_GRDbar_R
import Definitions.Def_GreedyReusableNet_thresholdLaw

open MeasureTheory

namespace GreedyReusableNet

/-- **The first line of the final chains** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, proof of
Theorem 2, p.42: "`Rew(GRD-R) = 𝔼_r[Rew(GRD(r))]`"; p.43: "`Rew(GRD̄-R) = 𝔼_r̄[Rew(GRD̄(r̄))]`").

For `0 < a ≤ b` and any oracle: the expected reward of GRD-R with threshold law `G` on `[a, b]`
equals the `G`-average of the expected rewards of `GRD(r)`, and likewise for GRD̄-R and `GRD̄(r̄)`.

**Formalization Note** GRD-R draws its threshold inside the run (as its initial seed), so this
is an interchange of integrals over the threshold and the tape, not a definition. -/
theorem rew_GRD_R_eq_integral {N T : ℕ} (I : ProblemInstance N) (O : Oracle N)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Rew I T (GRD_R I O a b) = ∫ r, Rew I T (GRD I O r) ∂(thresholdLaw a b) ∧
      Rew I T (GRDbar_R I O a b) = ∫ r, Rew I T (GRDbar I O r) ∂(thresholdLaw a b) := by sorry

end GreedyReusableNet
