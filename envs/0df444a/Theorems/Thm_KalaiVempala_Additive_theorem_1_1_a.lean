-- Prove2me | Theorems.Thm_KalaiVempala_Additive_theorem_1_1_a
-- name    : KalaiVempala.Additive.theorem_1_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:10.40995+00:00
-- url     : https://prove2.me/theorems/1250c372-cd5a-424e-bc5c-79fa062aef9e
-- title:
--   Theorem 1.1(a), p. 294 — E[cost of FPL(ε)] ≤ min-cost_T + εRAT + D/ε
-- statement:
--   **Additive regret bound for Follow the Perturbed Leader.** Let $\mathcal D, \mathcal S \subset \mathbb R^n$ be the decision and state sets, and let $M$ be an argmin oracle for $\mathcal D$, so that $M(x) \in \mathcal D$ minimises $d \cdot x$ over $\mathcal D$. Let the parameters $D$, $R$, $A$ satisfy
--
--   1. $D \ge |d - d'|_1$ for all $d, d' \in \mathcal D$ (the diameter),
--   2. $R \ge |d \cdot s|$ for all $d \in \mathcal D$, $s \in \mathcal S$,
--   3. $A \ge |s|_1$ for all $s \in \mathcal S$,
--
--   where $|x|_1 = \sum_i |x_i|$. Let $s_1, \dots, s_T \in \mathcal S$ be a state sequence, $s_{1:t} = s_1 + \dots + s_t$, and $\text{min-cost}_T = \min_{d \in \mathcal D} \sum_{t=1}^T d \cdot s_t = M(s_{1:T}) \cdot s_{1:T}$.
--
--   The algorithm FPL($\varepsilon$) on each period $t$ chooses $p_t$ uniformly at random from the cube $[0, 1/\varepsilon]^n$ and uses the decision $M(s_{1:t-1} + p_t)$. Then for $0 < \varepsilon \le 1$,
--
--   $$\mathbb E[\text{cost of FPL}(\varepsilon)] \;\le\; \text{min-cost}_T + \varepsilon R A T + \frac{D}{\varepsilon}.$$
--
--   Choosing $\varepsilon = \sqrt{D/(RAT)}$ gives expected regret at most $2\sqrt{DRAT}$, using only $T$ calls to the offline oracle $M$.
--
--   **Formalization Note** The expected cost is `fplExpectedReward M s ε T` from `OracleRO.ApproxFPL.FPL`, namely $\sum_{t=1}^T \int s_t \cdot M(s_{1:t-1} + p)\, dU(p)$ with $U$ uniform on $[0, 1/\varepsilon]^n$ (the name says "Reward" because its source maximises; with an argmin oracle it is the expected cost, and $s_t \cdot M(\cdot) = M(\cdot) \cdot s_t$). The sum of per-period expectations is the expected total cost whether the $p_t$ are drawn afresh or shared, as the paper notes; the state sequence is fixed in advance. Added hypotheses: $\varepsilon > 0$ (the page divides by $\varepsilon$) and measurability of $M$, which with the bound $R$ makes every integrand bounded and measurable, so every expectation is a genuine integral. The page's $\varepsilon \le 1$ is kept although the bound does not need it. $T$ is arbitrary; at $T = 0$ the claim is $0 \le D/\varepsilon$. States are indexed from $1$ and `s 0` is unused.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 294, Theorem 1.1(a); model and parameters pp. 293–294

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Additive

theorem theorem_1_1_a {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam R A : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (hR : ∀ d ∈ Dset, ∀ x ∈ S, |d ⬝ᵥ x| ≤ R) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hs : ∀ t ∈ Finset.Icc 1 T, s t ∈ S)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    fplExpectedReward M s ε T ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T + ε * R * A * T + Ddiam / ε := by sorry

end KalaiVempala.Additive
