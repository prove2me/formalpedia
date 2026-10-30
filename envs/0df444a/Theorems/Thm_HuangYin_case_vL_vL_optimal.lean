-- Prove2me | Theorems.Thm_HuangYin_case_vL_vL_optimal
-- name    : HuangYin.case_vL_vL_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:48:14.999603+00:00
-- url     : https://prove2.me/theorems/0ad88ec2-0b1f-4230-a64a-d9b72d42a48c
-- title:
--   At $p_1=p_2=v_L$ the firm offers only product $L$
-- statement:
--   When $p_1=p_2=v_L$ every customer buys in both periods, and the profit (2) is
--
--   $$\Pi(\xi_1,\xi_2\mid v_L,v_L)=[v_L-\xi_1c_H-(1-\xi_1)c_L]+[v_L-\xi_2c_H-(1-\xi_2)c_L].\qquad(6)$$
--
--   The offering probabilities $\xi_1=\xi_2=0$ maximize it over $[0,1]^2$: at these prices the firm uses transparent selling of product $L$.
--
--   Differences from the source:
--
--   - encoding: K anecdotes per customer and a prior belief ξ0 (p. 8), with ξ0 = 0 from p. 9 on and K = 1 in §4 → the estimate (ξ0 + anecdote)/(K + 1) with K = 1, ξ0 = 0 built into `estimate`; the purchasing fractions derived from rule (1) in `demand`; reason: §4 and the result fix K = 1 and the paper fixes ξ0 = 0; the derived fractions are Lemma 1's γ's for K = 1 (1 at vL, ξ at vHL, 0 above vHL), so no instance changes
--   - reading: 'the optimal product offering decisions are' / 'it is optimal to use' → the stated choice is feasible and attains the maximum (`OptimalOffer`, `IsOptimal`), not that it is the unique maximizer; reason: Proposition 1 (iii) calls both transparent policies optimal when vH − cH = vL − cL, so optimality cannot mean uniqueness
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), p. 13, after equation (6) (unnumbered)

import Mathlib
import Definitions.Def_HuangYin_OptimalOffer

namespace HuangYin

/-- **At `p1 = p2 = vL` the firm offers only product `L`** (p. 13, after equation (6); unnumbered).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), p. 13: "Clearly, the optimal product offering decisions are ξ1 = ξ2 = 0. That is, the
firm uses a transparent selling policy for product L only in this case."

At the prices `p1 = p2 = vL` the offering probabilities `ξ1 = ξ2 = 0` maximize the profit (2)
over `[0,1]²`. -/
theorem case_vL_vL_optimal (P : Params) : OptimalOffer P P.vL P.vL 0 0 := by sorry

end HuangYin
