-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_7
-- name    : InvestCommonGood.MixedTSSPE.lemma_B_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:42.016615+00:00
-- url     : https://prove2.me/theorems/6e1439a4-0941-4edc-a322-2b9c9e3ec45d
-- title:
--   Lemma B.7, EC p. 19 — functions satisfying the §4.2 conditions are the payoffs of ν*
-- statement:
--   Let the standing assumptions and Assumptions 1 and 2 hold, let the costs satisfy $0<c_2<c_1$, let $q\in(0,1)$, and let $U_1,V_1,V_2$ satisfy the conditions of §4.2 for the threshold $\theta^*$, targets $(z_1,z_2)$ and probability $q$. Let the randomization devices be independent uniform randomizers and fair tie coins, and let $\nu^*$ use the rates $\lambda_i$ of (29) built from $F_{1,0}=U_1$, $F_{2,0}=V_2$. Then for every initial state $x\in\mathcal I$ and every play of $\nu^*$ from $x$:
--   1. both players' payoffs (22) are well defined;
--   2. player 2's payoff is $V_2(x)$;
--   3. player 1's payoff is $U_1(x)$ if the game starts in the first stage and $V_1(x)$ if it starts in the second stage.
--
--   In the paper's notation, $F_1$ and $F_2$ are the payoff functions associated with $\nu^*$; this is the half of the verification theorem that identifies the candidate functions with equilibrium payoffs.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, EC p. 19 (PDF 50), Lemma B.7

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem lemma_B_7 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (zs θ q : ℝ) (c z : Fin 2 → ℝ) (U1 V1 V2 : ℝ → ℝ)
    (hS : Standing m S) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hc : 0 < c 1) (hc12 : c 1 < c 0) (hq0 : 0 < q) (hq1 : q < 1)
    (hF : Sec42 m S c θ z q U1 V1 V2)
    (Rd : Rand Ω) (hRd : RandStanding S Rd) :
    Induces m S Rd c θ q z (rate29 m ![U1, V2] c z θ) U1 V1 V2 := by sorry

end InvestCommonGood.MixedTSSPE
