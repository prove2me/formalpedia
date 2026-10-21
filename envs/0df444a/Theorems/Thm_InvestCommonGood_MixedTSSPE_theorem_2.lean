-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_theorem_2
-- name    : InvestCommonGood.MixedTSSPE.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:28.722141+00:00
-- url     : https://prove2.me/theorems/a915b77e-8464-45ad-9fe2-97edab298294
-- title:
--   Theorem 2, p. 22 — verification theorem: §4.2 functions F₁, F₂ make ν* a subgame perfect equilibrium
-- statement:
--   Let the standing assumptions and Assumptions 1 and 2 hold, let the costs satisfy $0<c_2<c_1$, let $q\in(0,1)$, and suppose that functions $F_1=(U_1\mid V_1)$ and $F_2=V_2$ satisfying all the conditions of §4.2 exist for the threshold $\theta^*$ and targets $(z_1,z_2)$. Then for any randomization devices consisting of independent uniform randomizers and fair tie coins, the strategy profile $\nu^*$ — player 2 invests with probability $q$ when $X$ reaches $\theta^*$ from above in the first stage, and each player $i$ invests at the hazard rate $\lambda_i(X_t)$ of (29) in the second stage, always boosting to $z_i$ — is a subgame perfect equilibrium.
--
--   This is the first verification theorem for a mixed strategy equilibrium of an impulse control game; it reduces the existence question to the analytic conditions of §4.2.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, p. 22, Theorem 2

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (zs θ q : ℝ) (c z : Fin 2 → ℝ) (U1 V1 V2 : ℝ → ℝ)
    (hS : Standing m S) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hc : 0 < c 1) (hc12 : c 1 < c 0) (hq0 : 0 < q) (hq1 : q < 1)
    (hF : Sec42 m S c θ z q U1 V1 V2) :
    ∀ Rd : Rand Ω, RandStanding S Rd → IsSPE m S Rd c θ q z (rate29 m ![U1, V2] c z θ) := by sorry

end InvestCommonGood.MixedTSSPE
