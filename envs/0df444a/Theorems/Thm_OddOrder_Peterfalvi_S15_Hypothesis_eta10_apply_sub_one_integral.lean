-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_eta10_apply_sub_one_integral
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.eta10_apply_sub_one_integral
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:46:11.339393+00:00
-- url     : https://prove2.me/theorems/b5f8b5f7-165d-49e4-8240-c41fac0477f9
-- title:
--   Peterfalvi (13.7): $\eta_{10}(y)\equiv1\pmod{(1-\varepsilon)}$ for $y\in W_2^\#$
-- statement:
--   Let $G$ be a finite group and `hyp : Hypothesis` the Peterfalvi (13.1) configuration (with $q=|W_1|$ prime). Let $\varepsilon\in\mathbb C$ be a primitive $q$-th root of unity and $y\in W_2$ with $y\ne1$. Then there is $z\in\mathbb C$, integral over $\mathbb Z$, with
--
--   $$\eta_{10}(y)-1=(1-\varepsilon)\,z ,$$
--
--   where $\eta_{10}=$ `hyp.eta10`.
--
--   This is the (1.10) congruence used in (13.7).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean#L1012-L1070

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem Hypothesis.eta10_apply_sub_one_integral [Finite G] (hyp : Hypothesis (G := G))
    {ε : ℂ} (hε : IsPrimitiveRoot ε hyp.q) {y : G} (hyW2 : y ∈ hyp.W2) (hy1 : y ≠ 1) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ hyp.eta10 y - 1 = (1 - ε) * z := by sorry

end OddOrder.Peterfalvi.S15
