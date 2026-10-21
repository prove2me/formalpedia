-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_8
-- name    : InvestCommonGood.MixedTSSPE.lemma_B_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:26.910947+00:00
-- url     : https://prove2.me/theorems/95456d5a-60f7-4dd2-b59c-ecb416c0b07a
-- title:
--   Lemma B.8, EC pp. 21–22 — q ∈ (0,1), θ* < x̂ < z₁ < z₂ and (B.21)–(B.23) give a mixed strategy TSSPE
-- statement:
--   Let the standing assumptions and Assumptions 1, 2, 4 and 5 hold, with $0<c_2<c_1$, let $\hat x$ be the point of Lemma 2, and suppose that $q\in(0,1)$ and $\theta^*<\hat x<z_1<z_2$ satisfy
--   $$J(z_1)-J(\theta^*)=c_1,\qquad \frac{\varphi(\theta^*)[I(\theta^*)-I(z_1)]}{-I(z_1)\varphi(z_2)+(R_r\pi)(z_2)+I(\theta^*)\varphi(\theta^*)-(R_r\pi)(\theta^*)}=q,\qquad -I(z_1)\varphi(\theta^*)+(R_r\pi)(\theta^*)-k\theta^*<J(z_1).$$
--   Then there are functions $U_1,V_1,V_2$ satisfying all the conditions of §4.2 such that, for any independent uniform randomizers and fair tie coins, the profile $\nu^*$ characterized by $q,\theta^*,z_1,z_2$, with the rates (29) built from these functions, is a mixed strategy two-stage subgame perfect equilibrium.
--
--   In practice this lemma is the existence test: it reduces the equilibrium to three scalar conditions.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, EC pp. 21–22 (PDF 52–53), Lemma B.8

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem lemma_B_8 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c1 c2 zs xs θ z1 z2 xh q : ℝ)
    (hS : Standing m S) (hc2 : 0 < c2) (hc12 : c2 < c1) (hA1 : Assumption1 m S)
    (hA2 : Assumption2 m S zs) (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2)
    (hxh : IsLemma2Point m S xh) (hq0 : 0 < q) (hq1 : q < 1)
    (hθ : θ < xh) (hz1 : xh < z1) (hz12 : z1 < z2)
    (hB21 : Jfun m S z1 - Jfun m S θ = c1) (hB22 : qB22 m S θ z1 z2 = q)
    (hB23 : B23 m S θ z1) :
    ∃ U1 V1 V2 : ℝ → ℝ, Sec42 m S ![c1, c2] θ ![z1, z2] q U1 V1 V2 ∧
      ∀ Rd : Rand Ω, RandStanding S Rd →
        IsSPE m S Rd ![c1, c2] θ q ![z1, z2] (rate29 m ![U1, V2] ![c1, c2] ![z1, z2] θ) := by sorry

end InvestCommonGood.MixedTSSPE
