-- Prove2me | Theorems.Thm_GreedyRS_Tight_ec1_6_liminf_pics
-- name    : GreedyRS.Tight.ec1_6_liminf_pics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:28.28715+00:00
-- url     : https://prove2.me/theorems/ab387273-4dbd-4cde-8bf3-ecfb7978cca6
-- title:
--   (EC.1.6), p. ec3 — under the SC-CV, liminf_k PICS ≥ Pr{∃ n ≥ 1: X̄₁(n) < µ₁ − γ₀}
-- statement:
--   Assume the slippage configuration with a common variance: $\mu_1 - \mu_i = \gamma > 0$ for $i \ge 2$ and $\sigma_i^2 = \sigma^2 > 0$ for all $i$, with independent normal observations. Let the budget be $B = \lfloor ck \rfloor$ with $c > C(\gamma/\sigma)$, and let $\gamma_0 \in (0, \gamma)$ satisfy $C((\gamma - \gamma_0)/\sigma) = c$. Then the probability of incorrect selection of the greedy procedure satisfies
--   $$\liminf_{k\to\infty} \mathrm{PICS} \ge \Pr\{\exists\, n \ge 1 \text{ s.t. } \bar X_1(n) < \mu_1 - \gamma_0\}.$$
--
--   If the best alternative's running average ever drops below the boundary $\mu_1 - \gamma_0$, then for large $k$ an incorrect selection is (asymptotically) inevitable. Together with Theorem 1 this yields the limit in Theorem 2.
--
--   **Formalization Note.** The page writes the event both as $\{\min_{n\ge1} \bar X_1(n) < \mu_1 - \gamma_0\}$ and as $\{\exists n \ge 1: \bar X_1(n) < \mu_1 - \gamma_0\}$; the second is stated. The budget $ck$ is read as $\lfloor ck \rfloor$; alternatives are 0-based in Lean; probabilities and the liminf are in $[0,\infty]$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. ec3 (PDF 42), EC.1.4, Equation (EC.1.6)

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GreedyRS.Tight

theorem ec1_6_liminf_pics {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (γ : ℝ) (hγ : 0 < γ) (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ)
    (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / Real.sqrt w) < c)
    (γ0 : ℝ) (hγ0 : γ0 ∈ Set.Ioo 0 γ) (hC0 : GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c) :
    P {ω | ∃ n : ℕ, 1 ≤ n ∧ GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n < μ 0 - γ0}
      ≤ Filter.liminf
          (fun k : ℕ => P {ω | GreedyRS.Greedy.greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) ≠ 0}) atTop := by sorry

end GreedyRS.Tight
