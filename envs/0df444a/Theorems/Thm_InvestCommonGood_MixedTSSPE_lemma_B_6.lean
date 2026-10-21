-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_6
-- name    : InvestCommonGood.MixedTSSPE.lemma_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:20.855348+00:00
-- url     : https://prove2.me/theorems/db9fd311-deaa-4f9d-99ab-be8e0707513f
-- title:
--   Lemma B.6, EC p. 14 — if ν* induces payoffs satisfying the §4.2 conditions, then ν* is an SPE
-- statement:
--   Let the standing assumptions and Assumptions 1 and 2 hold, let $0<c_2<c_1$, $q\in(0,1)$, let $U_1,V_1,V_2$ satisfy the conditions of §4.2, and let the randomization devices be independent uniform randomizers and fair tie coins. Suppose that the strategy profile $\nu^*$, with the rates $\lambda_i$ of (29), induces the payoff functions $F_1=(U_1\mid V_1)$ and $F_2=V_2$: from every state and stage its plays have well-defined payoffs equal to $V_2(x)$ for player 2 and to $U_1(x)$ (first stage) or $V_1(x)$ (second stage) for player 1. Then $\nu^*$ is a subgame perfect equilibrium: from every state and stage, no admissible deviation of either player against the other's $\nu^*$ yields a larger payoff.
--
--   This is the domination half of the verification theorem; the quasi-variational inequalities (27) bound the value of every investment a deviator can make.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, EC p. 14 (PDF 45), Lemma B.6

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem lemma_B_6 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (zs θ q : ℝ) (c z : Fin 2 → ℝ) (U1 V1 V2 : ℝ → ℝ)
    (hS : Standing m S) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hc : 0 < c 1) (hc12 : c 1 < c 0) (hq0 : 0 < q) (hq1 : q < 1)
    (hF : Sec42 m S c θ z q U1 V1 V2)
    (Rd : Rand Ω) (hRd : RandStanding S Rd)
    (hInd : Induces m S Rd c θ q z (rate29 m ![U1, V2] c z θ) U1 V1 V2) :
    IsSPE m S Rd c θ q z (rate29 m ![U1, V2] c z θ) := by sorry

end InvestCommonGood.MixedTSSPE
