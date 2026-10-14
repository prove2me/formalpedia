-- Prove2me | Theorems.Thm_GreedyRS_Tight_ec1_11_liminf_pics
-- name    : GreedyRS.Tight.ec1_11_liminf_pics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:41.890689+00:00
-- url     : https://prove2.me/theorems/0f43728c-25bd-4ddc-8f08-141c5a1c6b89
-- title:
--   (EC.1.11) with (EC.1.7), p. ec5 — liminf_k PICS ≥ Pr{m_ϵ < ∞, min_{1≤n≤m_ϵ−1} X̄₁(n) ≥ µ₁ − γ_ϵ⁻}
-- statement:
--   Assume the **slippage configuration with a common variance** (SC-CV): $\mu_1 - \mu_i = \gamma > 0$ for all $i \ge 2$ and $\sigma_i^2 = \sigma^2 > 0$ for all $i$, with independent normal observations. Let the budget be $B = \lfloor ck \rfloor$ with $c > C(\gamma/\sigma)$, fix $\epsilon$ with $0 < 2\epsilon < c - C(\gamma/\sigma)$, and let $\gamma_\epsilon^-, \gamma_\epsilon^+ \in (0, \gamma)$ satisfy (EC.1.7):
--   $$C\Big(\frac{\gamma - \gamma_\epsilon^-}{\sigma}\Big) = c - 2\epsilon, \qquad C\Big(\frac{\gamma - \gamma_\epsilon^+}{\sigma}\Big) = c + 2\epsilon.$$
--   With $m_\epsilon = \inf\{n \ge 1 : \bar X_1(n) < \mu_1 - \gamma_\epsilon^+\}$, the probability of incorrect selection of the greedy procedure satisfies
--   $$\liminf_{k\to\infty} \mathrm{PICS} \ge \Pr\Big\{ m_\epsilon < \infty,\ \min_{1\le n\le m_\epsilon-1} \bar X_1(n) \ge \mu_1 - \gamma_\epsilon^- \Big\}.$$
--
--   This is the $\epsilon$-approximate form of the lower bound on PICS; letting $\epsilon \to 0$ gives (EC.1.6).
--
--   **Formalization Note.** The budget $ck$ is read as $\lfloor ck \rfloor$. The minimum over $1 \le n \le m_\epsilon - 1$ is written pointwise ("$\bar X_1(n) \ge \mu_1 - \gamma_\epsilon^-$ for every $1 \le n \le m_\epsilon - 1$"), which is vacuous when $m_\epsilon = 1$, matching the paper's convention $\bar X_1(0) = \infty$. Probabilities and the liminf are in $[0,\infty]$. Alternatives are 0-based in Lean. $C$ is evaluated only at positive arguments.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. ec5 (PDF 44), Equation (EC.1.11); (EC.1.7) on p. ec3 (PDF 42)

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GreedyRS.Tight

theorem ec1_11_liminf_pics {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (γ : ℝ) (hγ : 0 < γ) (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ)
    (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / Real.sqrt w) < c)
    (ε : ℝ) (hε : 0 < 2 * ε ∧ 2 * ε < c - GreedyRS.Greedy.Cfun (γ / Real.sqrt w))
    (γm γp : ℝ) (hγm : γm ∈ Set.Ioo 0 γ) (hγp : γp ∈ Set.Ioo 0 γ)
    (hCm : GreedyRS.Greedy.Cfun ((γ - γm) / Real.sqrt w) = c - 2 * ε)
    (hCp : GreedyRS.Greedy.Cfun ((γ - γp) / Real.sqrt w) = c + 2 * ε) :
    P {ω | ∃ m : ℕ, GreedyRS.Greedy.crossBelow (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) (μ 0 - γp) 1 = m ∧
        ∀ n ∈ Finset.Icc 1 (m - 1), μ 0 - γm ≤ GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n}
      ≤ Filter.liminf
          (fun k : ℕ => P {ω | GreedyRS.Greedy.greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) ≠ 0}) atTop := by sorry

end GreedyRS.Tight
