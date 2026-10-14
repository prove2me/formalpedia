-- Prove2me | Theorems.Thm_GMCPBandit_Regret_lemma_EC_8_2
-- name    : GMCPBandit.Regret.lemma_EC_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:37.256381+00:00
-- url     : https://prove2.me/theorems/55593891-d182-4eb1-a4b9-8a26060c58ee
-- title:
--   Lemma EC.8 (2), p. ec16 — ℙ{|𝒜| < ¼p*C₀log(T+1)} ≤ 1/(T+1) for the random samples in U_k
-- statement:
--   Work in the model of §3 with $\mathcal P_x(U_k)\ge p^*$ for every optimal decision $k\in\mathcal K_o$ (Assumption A.3). Let $C_0=\max\{10,16/p^*\}$, $t_0=2C_0|\mathcal K|$ and $T\ge\max\{(t_0+1)^2/e^2-1,\,e\}$. For $k\in\mathcal K_o$ let $\mathcal A$ be the set of random samples of decision $k$ up to time $T$ (times $s\le T$ with $\mathcal D_s=1$ and decision $k$ drawn) whose covariate lies in $U_k$. Then
--   $$\mathbb P\Big\{|\mathcal A|<\tfrac14p^*C_0\log(T+1)\Big\}\le\frac{1}{T+1}.$$
--
--   The random samples of an optimal decision that fall in its region $U_k$ are i.i.d. draws from the conditional law on $U_k$, on which the restricted eigenvalue condition holds; this lemma guarantees there are logarithmically many of them.
--
--   **Formalization Note** The page lists Assumptions A.3 and A.4; the statement uses only A.3 (and the measurability of $U_k$ provided by the reward family), so A.4 is omitted, which makes the statement stronger. The claim is made for $k\in\mathcal K_o$, where $U_k$ has probability at least $p^*$.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, p. ec16, Lemma EC.8, statement 2

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

/-- **Lemma EC.8, statement 2** (p. ec16). Let `C₀ = max{10, 16/p*}`, `t₀ = 2C₀|𝒦|` and
`T ≥ max{(t₀+1)²/e² − 1, e}`. For a decision `k ∈ 𝒦_o`, the number `|𝒜|` of random samples of `k`
up to time `T` whose covariate lies in `U_k` satisfies `ℙ{|𝒜| < ¼ p* C₀ log(T+1)} ≤ 1/(T+1)`. -/
theorem lemma_EC_8_2 {d K : ℕ} (hd : 1 ≤ d) (hK : 2 ≤ K)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (Rmax h pstar : ℝ) (Ko Ks : Finset (Fin K))
    (hglm : IsGLMFamily ν g Rmax) (hA3 : A3 𝒳 PX ν g β Ko Ks h pstar)
    (C0 t0 : ℝ) (hC0 : C0 = max 10 (16 / pstar)) (ht0 : t0 = 2 * C0 * K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (hprim : IsPrimitives P 𝒳 PX ν g β Rmax X R V A)
    (T : ℕ) (hT : max ((t0 + 1) ^ 2 / Real.exp 1 ^ 2 - 1) (Real.exp 1) ≤ (T : ℝ))
    (k : Fin K) (hk : k ∈ Ko) :
    P {ω | ((randomSamplesIn t0 (fun s => V s ω) (fun s => A s ω) (fun s => X s ω)
              (optRegion 𝒳 ν g β h k) k T).card : ℝ) <
            1 / 4 * pstar * C0 * Real.log ((T : ℝ) + 1)} ≤
      ENNReal.ofReal (1 / ((T : ℝ) + 1)) := by sorry

end GMCPBandit.Regret
