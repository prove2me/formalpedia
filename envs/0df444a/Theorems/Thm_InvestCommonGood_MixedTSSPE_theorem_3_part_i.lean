-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_theorem_3_part_i
-- name    : InvestCommonGood.MixedTSSPE.theorem_3_part_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:53.409631+00:00
-- url     : https://prove2.me/theorems/da620c9b-c903-4c25-9999-ea802baa1e0d
-- title:
--   Proof of Theorem 3, part (i), EC p. 26 — for c₁ near c₂ there are z₁ ∈ [x̂, z₂) with (B.21) and q ∈ (0,1) with (B.22)
-- statement:
--   Let the standing assumptions and Assumptions 1, 2, 4 and 5 hold, with $c_2>0$, and let $\hat x$ be the point of Lemma 2. Then there is $\hat c>c_2$ such that for every $c_1\in(c_2,\hat c)$ there exists $z_1\in[\hat x,z_2)$ with
--   $$J(z_1)-J(\theta^*)=c_1,\qquad 0<\frac{\varphi(\theta^*)[I(\theta^*)-I(z_1)]}{-I(z_1)\varphi(z_2)+(R_r\pi)(z_2)+I(\theta^*)\varphi(\theta^*)-(R_r\pi)(\theta^*)}<1 .$$
--
--   So (B.21) has a solution and the probability $q$ defined by (B.22) is a genuine mixing probability when the asymmetry $c_1-c_2$ is small.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, proof of Theorem 3, part (i), EC p. 26 (PDF 57)

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem theorem_3_part_i {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c2 zs xs θ z2 xh : ℝ)
    (hS : Standing m S) (hc2 : 0 < c2) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2) (hxh : IsLemma2Point m S xh) :
    ∃ chat : ℝ, c2 < chat ∧ ∀ c1 ∈ Ioo c2 chat, ∃ z1 ∈ Ico xh z2,
      Jfun m S z1 - Jfun m S θ = c1 ∧ 0 < qB22 m S θ z1 z2 ∧ qB22 m S θ z1 z2 < 1 := by sorry

end InvestCommonGood.MixedTSSPE
