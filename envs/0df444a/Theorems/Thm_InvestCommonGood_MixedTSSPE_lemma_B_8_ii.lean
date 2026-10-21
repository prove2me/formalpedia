-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_8_ii
-- name    : InvestCommonGood.MixedTSSPE.lemma_B_8_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:51.715859+00:00
-- url     : https://prove2.me/theorems/3eab6a14-f734-4187-b6d6-fc4d6565fc97
-- title:
--   Lemma B.8, part (ii), EC pp. 24–26 — with (B.21)–(B.23), the explicit Û₁, V̂₁, V̂₂ satisfy all §4.2 conditions
-- statement:
--   Let the standing assumptions and Assumptions 1, 2, 4 and 5 hold, with $0<c_2<c_1$, let $\hat x$ be the point of Lemma 2, let $q\in(0,1)$ and $\theta^*<\hat x<z_1<z_2$, and suppose
--   $$J(z_1)-J(\theta^*)=c_1\ \ (\text{B.21}),\qquad \frac{\varphi(\theta^*)[I(\theta^*)-I(z_1)]}{-I(z_1)\varphi(z_2)+(R_r\pi)(z_2)+I(\theta^*)\varphi(\theta^*)-(R_r\pi)(\theta^*)}=q\ \ (\text{B.22}),$$
--   $$-I(z_1)\varphi(\theta^*)+(R_r\pi)(\theta^*)-k\theta^*<J(z_1)\ \ (\text{B.23}).$$
--   With $\alpha=-I(\theta^*)$, $\beta=-I(z_1)$, let $\hat V_1=\alpha\varphi+R_r\pi$ and $\hat U_1=\beta\varphi+R_r\pi$ on $[\theta^*,b)$, and $\hat U_1(x)=\hat V_1(x)=\hat U_1(z_1)-k(z_1-x)-c_1$ on $(a,\theta^*)$; let $\hat V_2$ be as in part (i). Then $(\hat U_1,\hat V_1,\hat V_2)$ satisfy all the conditions of §4.2 for the costs $(c_1,c_2)$, targets $(z_1,z_2)$, threshold $\theta^*$ and probability $q$.
--
--   Together with Theorem 2 this yields the mixed equilibrium of Lemma B.8.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, proof of Lemma B.8, part (ii), EC pp. 24–26 (PDF 55–57)

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem lemma_B_8_ii {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c1 c2 zs xs θ z1 z2 xh q : ℝ)
    (hS : Standing m S) (hc2 : 0 < c2) (hc12 : c2 < c1) (hA1 : Assumption1 m S)
    (hA2 : Assumption2 m S zs) (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2)
    (hxh : IsLemma2Point m S xh) (hq0 : 0 < q) (hq1 : q < 1)
    (hθ : θ < xh) (hz1 : xh < z1) (hz12 : z1 < z2)
    (hB21 : Jfun m S z1 - Jfun m S θ = c1) (hB22 : qB22 m S θ z1 z2 = q)
    (hB23 : B23 m S θ z1) :
    Sec42 m S ![c1, c2] θ ![z1, z2] q
      (Uhat1 m S c1 θ z1) (Vhat1 m S c1 θ z1) (Vhat2 m S c2 θ z2) := by sorry

end InvestCommonGood.MixedTSSPE
