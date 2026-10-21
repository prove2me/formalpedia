-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_theorem_3
-- name    : InvestCommonGood.MixedTSSPE.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:43.800994+00:00
-- url     : https://prove2.me/theorems/6f5bd148-c11b-4fa8-a963-cfe56460322b
-- title:
--   Theorem 3, p. 24 — for c₁ ∈ (c₂, ĉ) a mixed strategy TSSPE ν*(θ*, z₁, z₂, q) exists, q ∈ (0,1), θ* < x̂ < z₁ < z₂
-- statement:
--   Consider the impulse game of investment in a common good: the stock follows $dX_t=\mu(X_t)dt+\sigma(X_t)dW_t$ on $\mathcal I=(a,b)$, both players earn the flow profit $\pi(X_t)$ discounted at rate $r$, and player $i$ may invest at any time, paying $c_i+k\zeta$ to raise the stock by $\zeta\ge0$; simultaneous attempts are settled by a fair coin. Let the standing assumptions and Assumptions 1, 2, 4 and 5 hold, with $c_2>0$ and $\theta^*<z_2$ the points of Assumption 5. Then there is $\hat c>c_2$ such that for every $c_1\in(c_2,\hat c)$ there exist $z_1$ and $q$ with
--   $$0<q<1,\qquad \theta^*<\hat x<z_1<z_2,$$
--   where $\hat x$ is the point of Lemma 2, and functions $U_1,V_1,V_2$ satisfying all the conditions of §4.2, such that for any independent uniform randomizers and fair tie coins the strategy profile $\nu^*$ characterized by $\theta^*,z_1,z_2,q$ — player 2 invests with probability $q$ when the stock reaches $\theta^*$ from above in the first stage; in the second stage each player $i$ invests at the hazard rate $\lambda_i(X_t)$ of (29), positive exactly on the common mixed region $(a,\theta^*)$; every investment of player $i$ raises the stock to $z_i$ — is a subgame perfect equilibrium.
--
--   In contrast to the single-investment game, where any asymmetry $c_1\ne c_2$ destroys the mixed equilibrium (Theorem 1), repeated investment sustains a mixed strategy equilibrium under moderate asymmetry.
--
--   **Formalization Note.** "Mixed strategy TSSPE characterized by $\theta^*,z_1,z_2,q$" is stated as: the §4.2 profile with these parameters and the rates (29) of functions satisfying the §4.2 conditions is a subgame perfect equilibrium of the randomized game (Nash from every state and stage), with $q\in(0,1)$. The existence of plays is not posed; the equilibrium property holds for every play.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, p. 24, Theorem 3

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 zs xs θ z2 : ℝ)
    (hS : Standing m S) (hc2 : 0 < c2) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2) :
    ∃ chat : ℝ, c2 < chat ∧ ∀ c1 ∈ Ioo c2 chat, ∃ z1 q : ℝ, ∃ U1 V1 V2 : ℝ → ℝ,
      0 < q ∧ q < 1 ∧ (∃ xh : ℝ, IsLemma2Point m S xh ∧ θ < xh ∧ xh < z1) ∧ z1 < z2 ∧
      Sec42 m S ![c1, c2] θ ![z1, z2] q U1 V1 V2 ∧
      ∀ Rd : Rand Ω, RandStanding S Rd →
        IsSPE m S Rd ![c1, c2] θ q ![z1, z2] (rate29 m ![U1, V2] ![c1, c2] ![z1, z2] θ) := by sorry

end InvestCommonGood.MixedTSSPE
