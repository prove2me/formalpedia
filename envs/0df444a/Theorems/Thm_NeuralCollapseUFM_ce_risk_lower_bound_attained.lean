-- Prove2me | Theorems.Thm_NeuralCollapseUFM_ce_risk_lower_bound_attained
-- name    : NeuralCollapseUFM.ce_risk_lower_bound_attained
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:17:57.306792+00:00
-- url     : https://prove2.me/theorems/73c77069-1a82-439d-a011-f0d00b48b31b
-- title:
--   Lemma B.4: when the lower bound of Lemma B.3 is attained
-- statement:
--   Under the assumptions of Lemma B.3 ($K\ge2$, $n\ge1$, $\lambda_W,\lambda_H,\lambda_b>0$, $(W,H,b)$ a critical point of $f$, $\rho=\|W\|_F^2$, $c_1>0$), the lower bound
--
--   $$g(WH+b1^\top)\ge-\frac{\rho}{(1+c_1)(K-1)}\sqrt{\frac{\lambda_W}{\lambda_Hn}}+c_2$$
--
--   is attained if and only if all of the following hold:
--
--   1. $\|w^1\|_2=\|w^2\|_2=\cdots=\|w^K\|_2$;
--   2. $b=b1$ for some $b\in\mathbb{R}$;
--   3. $\bar h_i:=\frac1K\sum_{j=1}^Kh_{j,i}=0$ for all $i\in[n]$;
--   4. $\sqrt{\lambda_W/(\lambda_Hn)}\,w^k=h_{k,i}$ for all $k\in[K]$, $i\in[n]$;
--   5. $WW^\top=\frac{\rho}{K-1}\big(I_K-\frac1K1_K1_K^\top\big)$;
--   6. $c_1=\Big[(K-1)\exp\Big(-\frac{\rho}{K-1}\sqrt{\frac{\lambda_W}{\lambda_Hn}}\Big)\Big]^{-1}$.
--
--   These are the equality conditions (a)-(e) of the proof of Theorem 3.1.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Appendix B.2, Lemma B.4, p. 34 (bound (19), p. 32)

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem ce_risk_lower_bound_attained {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x) (c1 : ℝ)
    (hc1 : 0 < c1) :
    ceRisk (logits x.1 x.2.1 x.2.2) =
        -(frobSq x.1) / ((1 + c1) * ((K : ℝ) - 1)) * Real.sqrt (lamW / (lamH * n)) + cTwo K c1 ↔
      (∀ k l, Real.sqrt (sqNorm (x.1 k)) = Real.sqrt (sqNorm (x.1 l))) ∧
      (∃ b0 : ℝ, x.2.2 = fun _ => b0) ∧
      (∀ i, (1 / (K : ℝ)) • (∑ j, fun r => x.2.1 r (j, i)) = 0) ∧
      (∀ k i, Real.sqrt (lamW / (lamH * n)) • x.1 k = fun r => x.2.1 r (k, i)) ∧
      x.1 * x.1ᵀ = (frobSq x.1 / ((K : ℝ) - 1)) • (1 - (1 / (K : ℝ)) • onesMat K) ∧
      c1 = (((K : ℝ) - 1) *
        Real.exp (-(frobSq x.1 / ((K : ℝ) - 1)) * Real.sqrt (lamW / (lamH * n))))⁻¹ := by sorry

end NeuralCollapseUFM
