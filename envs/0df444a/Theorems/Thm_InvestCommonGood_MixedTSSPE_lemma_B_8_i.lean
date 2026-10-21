-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_8_i
-- name    : InvestCommonGood.MixedTSSPE.lemma_B_8_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:29.915847+00:00
-- url     : https://prove2.me/theorems/b7ef19a8-5f0e-4d51-891e-bf8b43104fa5
-- title:
--   Lemma B.8, part (i), EC pp. 22–24 — the explicit V̂₂ satisfies every §4.2 condition on V₂
-- statement:
--   Let the standing assumptions and Assumptions 1, 2, 4 and 5 hold, with $c_2>0$, let $\hat x$ be the point of Lemma 2, and suppose $\theta^*<\hat x<z_2$. With $\alpha=-I(\theta^*)$ define
--   $$\hat V_2(x)=\begin{cases}\alpha\varphi(z_2)+(R_r\pi)(z_2)-k(z_2-x)-c_2,&x\in(a,\theta^*],\\ \alpha\varphi(x)+(R_r\pi)(x),&x\in(\theta^*,b).\end{cases}$$
--   Then $\hat V_2$ satisfies every condition of §4.2 on player 2's payoff function $V_2$: it lies in $C^2(\mathcal I\setminus\{\theta^*\})\cap C^1(\mathcal I)$, exceeds $R_r\pi$, satisfies (24), (25) and the quasi-variational inequality (27), has $z_2$ as the unique maximizer of $\hat V_2(z)-kz$, equals $g_2$ below $\theta^*$, and has the form (30) above $\theta^*$ with $w_2=\alpha>0$.
--
--   This is the player-2 half of the existence of payoff functions certifying the mixed equilibrium; $\hat V_2$ is the value of the single-player impulse problem with cost $c_2$.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, proof of Lemma B.8, part (i), EC pp. 22–24 (PDF 53–55)

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem lemma_B_8_i {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 zs xs θ z2 xh : ℝ)
    (hS : Standing m S) (hc2 : 0 < c2) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2) (hxh : IsLemma2Point m S xh)
    (hθ : θ < xh) (hz2 : xh < z2) :
    Sec42V2 m S c2 θ z2 (Vhat2 m S c2 θ z2) := by sorry

end InvestCommonGood.MixedTSSPE
