-- Prove2me | Theorems.Thm_KalaiVempala_Multiplicative_fpl_star_bound
-- name    : KalaiVempala.Multiplicative.fpl_star_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:42.273396+00:00
-- url     : https://prove2.me/theorems/de1f6a84-8607-4306-a501-2c735c0ddc99
-- title:
--   P. 303 — E[cost of FPL*(ε)] ≤ (1 + 2εA)(min-cost_T + D(1 + ln n)/ε) for ε ≤ 1/A
-- statement:
--   Let $\mathcal D, \mathcal S \subset \mathbb R^n_+$ be nonnegative decision and state sets with $|d - d'|_1 \le D$ for $d, d' \in \mathcal D$ and $|s|_1 \le A$ for $s \in \mathcal S$, where $A > 0$. Let $M$ be a measurable argmin oracle for $\mathcal D$ and let $s_1, \dots, s_T \in \mathcal S$. Write $\text{min-cost}_T = M(s_{1:T})\cdot s_{1:T} = \min_{d\in\mathcal D} d\cdot s_{1:T}$. If $0 < \varepsilon \le 1/A$, then the algorithm FPL\*(ε), which on period $t$ plays $M(s_{1:t-1} + p_t)$ with $p_t$ drawn from the density $d\mu(x) \propto e^{-\varepsilon|x|_1}$, satisfies
--   $$\mathbb E[\text{cost of FPL}^*(\varepsilon)] \;\le\; (1 + 2\varepsilon A)\Big(\text{min-cost}_T + \frac{D(1 + \ln n)}{\varepsilon}\Big).$$
--
--   This is the multiplicative regret bound of FPL\* for an arbitrary parameter $\varepsilon \le 1/A$; Theorem 1.1(b) is its evaluation at $\varepsilon/2A$.
--
--   **Formalization Note** The expected cost is `fplStarExpectedCost M s ε T`, the sum over $t$ of the integrals of $s_t\cdot M(s_{1:t-1} + p)$ against the normalised law `laplaceLaw n ε`. Measurability of $M$, $\varepsilon > 0$ and $A > 0$ are added (the expectations presuppose the first; $\varepsilon \le 1/A$ presupposes the others). The bound $R$ of the paper is not used and is not a hypothesis. The states $s_t$ are indexed from $1$; $s_0$ is unused.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 303, proof of Theorem 1.1(b), the display after 'Finally, combining the above gives'

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem fpl_star_bound {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hs : ∀ t ∈ Finset.Icc 1 T, s t ∈ S)
    (hDnn : ∀ d ∈ Dset, ∀ i, 0 ≤ d i) (hSnn : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (hA0 : 0 < A) (ε : ℝ) (hε0 : 0 < ε) (hεA : ε ≤ 1 / A) :
    fplStarExpectedCost M s ε T ≤
      (1 + 2 * ε * A) * (M (prefixSum s T) ⬝ᵥ prefixSum s T + Ddiam * (1 + Real.log n) / ε) := by sorry

end KalaiVempala.Multiplicative
