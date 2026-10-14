-- Prove2me | Theorems.Thm_GMCPBandit_Regret_lemma_EC_8_3
-- name    : GMCPBandit.Regret.lemma_EC_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:43.393309+00:00
-- url     : https://prove2.me/theorems/015bf1fa-a3b0-4690-a856-543d769fe896
-- title:
--   Lemma EC.8 (3), p. ec16 — ℙ{|𝒜|/n < p*/24} ≤ 3/(T+1)
-- statement:
--   Under the hypotheses of Lemma EC.8, statement 2 ($C_0=\max\{10,16/p^*\}$, $t_0=2C_0|\mathcal K|$, $T\ge\max\{(t_0+1)^2/e^2-1,e\}$, $k\in\mathcal K_o$), let $n$ be the number of random samples of decision $k$ up to time $T$ and $\mathcal A$ those whose covariate lies in $U_k$. Then
--   $$\mathbb P\Big\{\frac{|\mathcal A|}{n}<\frac{1}{24}p^*\Big\}\le\frac{3}{T+1}.$$
--
--   A constant fraction of the random samples of an optimal decision lies in its region $U_k$.
--
--   **Formalization Note** The event is written multiplicatively, $|\mathcal A|<\frac{p^*}{24}n$. When $n=0$ the printed ratio is undefined and the multiplicative event is empty. As in statement 2, A.4 is not needed and is omitted.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, p. ec16, Lemma EC.8, statement 3

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

/-- **Lemma EC.8, statement 3** (p. ec16). Under the hypotheses of statement 2, the fraction of the
random samples of `k ∈ 𝒦_o` whose covariate lies in `U_k` satisfies `ℙ{|𝒜|/n < p*/24} ≤ 3/(T+1)`,
written multiplicatively as `|𝒜| < (p*/24) n`. -/
theorem lemma_EC_8_3 {d K : ℕ} (hd : 1 ≤ d) (hK : 2 ≤ K)
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
            1 / 24 * pstar * ((randomSet t0 (fun s => V s ω) (fun s => A s ω) k T).card : ℝ)} ≤
      ENNReal.ofReal (3 / ((T : ℝ) + 1)) := by sorry

end GMCPBandit.Regret
