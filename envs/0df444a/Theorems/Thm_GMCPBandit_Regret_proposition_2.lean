-- Prove2me | Theorems.Thm_GMCPBandit_Regret_proposition_2
-- name    : GMCPBandit.Regret.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:48.460606+00:00
-- url     : https://prove2.me/theorems/97d8110e-e268-480e-aa9e-f0ef71741ccb
-- title:
--   Proposition 2, p. 13 — under ε-decay sampling, C₀(1+log(T+1)−log(t₀+1)) ≤ n_k ≤ 3C₀(1+log T−log t₀) w.p. ≥ 1−2/(T+1)
-- statement:
--   Let $K\ge2$ decisions be explored by the ε-decay random sampling method: at each time $t\ge1$ a random sample is drawn with probability $\min\{1,t_0/t\}$, independently over time, and then a decision is chosen uniformly from $\mathcal K$. Let $n_k$ be the number of random samples of decision $k$ up to time $T$.
--
--   Let $C_0\ge10$, $t_0=2C_0|\mathcal K|$ and $T>(t_0+1)^2/e^2$. Then
--   $$\mathbb P\Big(C_0\big(1+\log(T+1)-\log(t_0+1)\big)\le n_k\le3C_0\big(1+\log T-\log t_0\big)\Big)\ge1-\frac{2}{T+1}.$$
--
--   The random sample size grows logarithmically in $T$; this is the source of the $\log T$ order of the regret.
--
--   **Formalization Note** The coin is $\mathcal D_t=\mathbb 1\{V_t\le\min\{1,t_0/t\}\}$ with $V_t\sim\mathrm{Unif}[0,1]$ and the uniform draw is $A_t$; the pairs $(V_t,A_t)$ are independent over $t$. $C_0$ is real, so $t_0$ need not be an integer.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, p. 13, Proposition 2

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

/-- **Proposition 2** (p. 13). Let `C₀ ≥ 10`, `t₀ = 2C₀|𝒦|` and `T > (t₀+1)²/e²`. Under the
ε-decay random sampling method, the random sample size `n_k = |ℛ_k(T)|` of decision `k` up to time
`T` satisfies `C₀(1 + log(T+1) − log(t₀+1)) ≤ n_k ≤ 3C₀(1 + log T − log t₀)` with probability at
least `1 − 2/(T+1)`. -/
theorem proposition_2 {K : ℕ} (hK : 2 ≤ K) (C0 t0 : ℝ) (hC0 : 10 ≤ C0) (ht0 : t0 = 2 * C0 * K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (hVA : IsExplorationCoins P V A)
    (T : ℕ) (hT : (t0 + 1) ^ 2 / Real.exp 1 ^ 2 < (T : ℝ)) (k : Fin K) :
    ENNReal.ofReal (1 - 2 / ((T : ℝ) + 1)) ≤
      P {ω | C0 * (1 + Real.log ((T : ℝ) + 1) - Real.log (t0 + 1)) ≤
              ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ) ∧
            ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ) ≤
              3 * C0 * (1 + Real.log (T : ℝ) - Real.log t0)} := by sorry

end GMCPBandit.Regret
