-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_theorem_3_part_ii
-- name    : InvestCommonGood.MixedTSSPE.theorem_3_part_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:30.581054+00:00
-- url     : https://prove2.me/theorems/3e9e85e1-ca2b-4fb5-9b82-45e709531012
-- title:
--   Proof of Theorem 3, part (ii), EC pp. 26–27 — (B.23) holds when c₁ is close to c₂
-- statement:
--   Let the standing assumptions and Assumptions 1, 2, 4 and 5 hold, with $c_2>0$, and let $\hat x$ be the point of Lemma 2. Then there is $\hat c>c_2$ such that for every $c_1\in(c_2,\hat c)$ and every $z_1\in[\hat x,z_2)$ with $J(z_1)-J(\theta^*)=c_1$,
--   $$-I(z_1)\varphi(\theta^*)+(R_r\pi)(\theta^*)-k\theta^*<J(z_1)\qquad(\text{B.23}).$$
--
--   Condition (B.23) says that player 1's best boost from the first-stage function is to $z_1$ rather than staying at $\theta^*$; it is the last scalar condition of Lemma B.8.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, proof of Theorem 3, part (ii), EC pp. 26–27 (PDF 57–58)

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem theorem_3_part_ii {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 zs xs θ z2 xh : ℝ)
    (hS : Standing m S) (hc2 : 0 < c2) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2) (hxh : IsLemma2Point m S xh) :
    ∃ chat : ℝ, c2 < chat ∧ ∀ c1 ∈ Ioo c2 chat, ∀ z1 ∈ Ico xh z2,
      Jfun m S z1 - Jfun m S θ = c1 → B23 m S θ z1 := by sorry

end InvestCommonGood.MixedTSSPE
