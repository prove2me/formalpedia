-- Prove2me | Theorems.Thm_GreedyRS_Tight_theorem1_sccv
-- name    : GreedyRS.Tight.theorem1_sccv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:33.138383+00:00
-- url     : https://prove2.me/theorems/9f9e94fe-9455-4abd-9f65-0a3f557aebee
-- title:
--   Theorem 1 under the SC-CV, p. 15 — liminf_k PCS ≥ Pr{min_n X̄₁(n) > µ₁ − γ₀} = [C(γ₀/σ)]⁻¹ > 0
-- statement:
--   Assume the slippage configuration with a common variance: $\mu_1 - \mu_i = \gamma > 0$ for $i = 2, 3, \dots$ and $\sigma_i^2 = \sigma^2 > 0$ for all $i$, with independent normal observations, so that Assumption 1 holds with $\bar\sigma = \sigma_1 = \sigma$. Let the budget be $B = \lfloor ck \rfloor$ with $c > C(\gamma/\sigma)$. Then there is $\gamma_0 \in (0, \gamma)$ with $C((\gamma - \gamma_0)/\sigma) = c$, and for every such $\gamma_0$ the PCS of the greedy procedure satisfies
--   $$\liminf_{k\to\infty} \mathrm{PCS} \ge \Pr\Big\{\min_{n\ge1} \bar X_1(n) > \mu_1 - \gamma_0\Big\} = \Big[C\Big(\frac{\gamma_0}{\sigma}\Big)\Big]^{-1} > 0.$$
--
--   This is the special case of Theorem 1 (sample optimality) that supplies the lower half of Theorem 2.
--
--   **Formalization Note.** The existence of $\gamma_0$, which the page leaves implicit, is stated as a conjunct so that the "for every such $\gamma_0$" part cannot hold vacuously. "$\min_{n\ge1} \bar X_1(n) > a$" is encoded as "the running average is bounded below and its infimum over $n \ge 1$ exceeds $a$" (the minimum is attained almost surely). The budget $ck$ is $\lfloor ck \rfloor$, ties go to the smallest index, alternatives are 0-based, and one observation array serves every $k$ (PCS for $k$ alternatives only depends on the first $k$ rows). If the general Theorem 1 is published on the platform, it implies this item.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 15, Theorem 1 (Assumption 1 instantiated by the SC-CV of §4.3, p. 16)

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GreedyRS.Tight

theorem theorem1_sccv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (γ : ℝ) (hγ : 0 < γ) (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ)
    (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / Real.sqrt w) < c) :
    (∃ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c →
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          ≤ Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k 1 ⌊c * k⌋₊) atTop ∧
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          = ENNReal.ofReal (1 / GreedyRS.Greedy.Cfun (γ0 / Real.sqrt w)) ∧
      0 < P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)} := by sorry

end GreedyRS.Tight
