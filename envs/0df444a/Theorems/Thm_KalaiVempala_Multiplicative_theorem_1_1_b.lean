-- Prove2me | Theorems.Thm_KalaiVempala_Multiplicative_theorem_1_1_b
-- name    : KalaiVempala.Multiplicative.theorem_1_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:42.748565+00:00
-- url     : https://prove2.me/theorems/d418c0e5-6156-4fa9-a13a-924cddec1996
-- title:
--   Theorem 1.1(b), p. 294 — for 𝒟, 𝒮 ⊂ ℝⁿ₊, E[cost of FPL*(ε/2A)] ≤ (1 + ε)min-cost_T + 4AD(1 + ln n)/ε
-- statement:
--   **Setting.** Decisions $d$ are chosen from a set $\mathcal D \subset \mathbb R^n$ and states $s$ from a set $\mathcal S \subset \mathbb R^n$; the cost of decision $d$ in state $s$ is $d\cdot s$. The decision set is accessed only through an offline oracle $M(x) = \arg\min_{d\in\mathcal D} d\cdot x$. The instance is measured by
--   $$D \ge |d - d'|_1 \ \ (d, d' \in \mathcal D), \qquad A \ge |s|_1 \ \ (s \in \mathcal S).$$
--   For a state sequence $s_1, \dots, s_T \in \mathcal S$ write $s_{1:t} = s_1 + \dots + s_t$ and $\text{min-cost}_T = \min_{d\in\mathcal D} d\cdot s_{1:T} = M(s_{1:T})\cdot s_{1:T}$.
--
--   **The algorithm.** FPL\*(η) on period $t$ draws $p_t$ from the density $d\mu(x) \propto e^{-\eta|x|_1}$ and plays $M(s_{1:t-1} + p_t)$.
--
--   **Theorem 1.1(b).** Suppose decisions and states are nonnegative, $\mathcal D, \mathcal S \subset \mathbb R^n_+$, and $A > 0$. For every $0 < \varepsilon \le 1$, every measurable argmin oracle $M$, and every state sequence $s_1, \dots, s_T \in \mathcal S$,
--   $$\mathbb E[\text{cost of FPL}^*(\varepsilon/2A)] \;\le\; (1 + \varepsilon)\,\text{min-cost}_T + \frac{4AD(1 + \ln n)}{\varepsilon}.$$
--
--   This is the multiplicative ("competitive") guarantee of Follow the Perturbed Leader: with exponentially distributed perturbations, the online cost is within a factor $1 + \varepsilon$ of the best fixed decision in hindsight, up to an additive term that does not grow with $T$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, $d\cdot s$ is `⬝ᵥ`, $|x|_1$ is written as $\sum_i |x_i|$; the decision set is `Dset` and the diameter `Ddiam`. The expected cost is `fplStarExpectedCost M s (ε / (2 * A)) T`, defined with the normalised law $(\eta/2)^n e^{-\eta|x|_1}$. Four hypotheses are added and disclosed: measurability of $M$ (the expectations presuppose it); $\varepsilon > 0$; $A > 0$ (the parameter $\varepsilon/2A$ presupposes it); and $\varepsilon \le 1$, which Theorem 1.1(b) does not state but its proof uses ("using the fact that $\varepsilon \le 1$ gives the theorem", p. 303). The bound $R \ge |d\cdot s|$ of the paper is not used by part (b) and is not a hypothesis. No hypothesis on $n$ is needed: $\ln n$ is `Real.log n`, and for $n = 0$ the statement is still the paper's with $\ln 0 := 0$.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 294, Theorem 1.1(b) (proof: p. 303, §4)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem theorem_1_1_b {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hs : ∀ t ∈ Finset.Icc 1 T, s t ∈ S)
    (hDnn : ∀ d ∈ Dset, ∀ i, 0 ≤ d i) (hSnn : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (hA0 : 0 < A) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    fplStarExpectedCost M s (ε / (2 * A)) T ≤
      (1 + ε) * (M (prefixSum s T) ⬝ᵥ prefixSum s T) + 4 * A * Ddiam * (1 + Real.log n) / ε := by sorry

end KalaiVempala.Multiplicative
