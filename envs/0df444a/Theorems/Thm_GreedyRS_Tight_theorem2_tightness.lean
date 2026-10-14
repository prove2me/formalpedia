-- Prove2me | Theorems.Thm_GreedyRS_Tight_theorem2_tightness
-- name    : GreedyRS.Tight.theorem2_tightness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:42.057194+00:00
-- url     : https://prove2.me/theorems/974f7e9f-d2dc-4c17-aede-ea083d76ea46
-- title:
--   Theorem 2, p. 16 — under the SC-CV with B = ⌊ck⌋ and c > C(γ/σ), lim_k PCS = Pr{min_n X̄₁(n) > µ₁ − γ₀} = [C(γ₀/σ)]⁻¹
-- statement:
--   Consider $k$ alternatives with independent normal observations $X_{ij} \sim N(\mu_i, \sigma_i^2)$, and assume the **slippage configuration with a common variance** (SC-CV): the non-best alternatives share one mean and all alternatives share one variance,
--   $$\mu_1 - \mu_i = \gamma > 0 \quad (i = 2, \dots, k), \qquad \sigma_i^2 = \sigma^2 > 0 \quad (i = 1, \dots, k).$$
--   Let $C(x) = \exp\big(\sum_{n\ge1} \frac1n \Phi(-\sqrt n\, x)\big)$ for $x > 0$. If the total budget is $B = \lfloor ck \rfloor$ with $c > C(\gamma/\sigma)$, then there exists $\gamma_0 \in (0, \gamma)$ with $C((\gamma - \gamma_0)/\sigma) = c$, and for every such $\gamma_0$ the PCS of the greedy procedure converges:
--   $$\lim_{k\to\infty} \mathrm{PCS} = \Pr\Big\{\min_{n\ge1} \bar X_1(n) > \mu_1 - \gamma_0\Big\} = \Big[C\Big(\frac{\gamma_0}{\sigma}\Big)\Big]^{-1}.$$
--
--   So the asymptotic lower bound of Theorem 1 is attained: under the SC-CV the limiting PCS of the greedy procedure is exactly the probability that the best alternative's running average stays above the boundary $\mu_1 - \gamma_0$.
--
--   **Formalization Note.** The budget "$B = ck$" is read as $\lfloor ck \rfloor$. Ties in every arg max go to the smallest index (a null event). Alternatives are 0-based in Lean (Lean's alternative $0$ is the paper's alternative $1$), and one infinite observation array serves every $k$. "$\min_{n\ge1} \bar X_1(n) > a$" is "bounded below with infimum $> a$". The existence of $\gamma_0$ is stated as a conjunct so the "for every such $\gamma_0$" part is not vacuous. The limit is taken in $[0, \infty]$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 16, Theorem 2; proof EC.1.4, pp. ec3–ec5 (PDF 42–44)

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GreedyRS.Tight

theorem theorem2_tightness {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (γ : ℝ) (hγ : 0 < γ) (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ)
    (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / Real.sqrt w) < c) :
    (∃ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c →
      Tendsto (fun k : ℕ => GreedyRS.Greedy.pcs P X k 1 ⌊c * k⌋₊) atTop
          (𝓝 (P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)})) ∧
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          = ENNReal.ofReal (1 / GreedyRS.Greedy.Cfun (γ0 / Real.sqrt w)) := by sorry

end GreedyRS.Tight
