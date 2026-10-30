-- Prove2me | Theorems.Thm_HuangYin_optimal_price_candidates
-- name    : HuangYin.optimal_price_candidates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:44:37.11607+00:00
-- url     : https://prove2.me/theorems/593e6d08-f308-4e8a-b3e0-d89ef860f225
-- title:
--   Opaque prices reduce to the candidates $v_L$ and $v_{HL}$
-- statement:
--   Consider the one-anecdote model. Every feasible opaque policy — offering probabilities $\xi_1,\xi_2\in[0,1]$, a first-period price $p_1\le v_{HL}$ and any second-period price $p_2$ — is weakly beaten by an opaque policy whose prices both lie in $\{v_L,v_{HL}\}$: there are $q_1,q_2\in\{v_L,v_{HL}\}$ and $x_1,x_2\in[0,1]$ with
--
--   $$\Pi(\xi_1,\xi_2\mid p_1,p_2)\le\Pi(x_1,x_2\mid q_1,q_2).$$
--
--   This is the reduction behind the paper's analysis of the four price cases (3)–(6): it justifies restricting the opaque prices to the two candidates.
--
--   Differences from the source:
--
--   - encoding: K anecdotes per customer and a prior belief ξ0 (p. 8), with ξ0 = 0 from p. 9 on and K = 1 in §4 → the estimate (ξ0 + anecdote)/(K + 1) with K = 1, ξ0 = 0 built into `estimate`; the purchasing fractions derived from rule (1) in `demand`; reason: §4 and the result fix K = 1 and the paper fixes ξ0 = 0; the derived fractions are Lemma 1's γ's for K = 1 (1 at vL, ξ at vHL, 0 above vHL), so no instance changes
--   - reading: 'the optimal price in each period should be chosen among the two candidates: vL and (vH−vL)/2 + vL' → every feasible opaque policy is weakly beaten by one with both prices in {vL, vHL}, with offering probabilities allowed to change; reason: this is what choosing the price among the candidates means; the probabilities must be allowed to change, because at p2 > vHL nobody buys in period 2 and the same ξ2 at p2 = vHL can earn a negative margin
--   - reading: prices p_t chosen freely (§3.2, 'optimizing the price p_t') → first-period opaque price restricted to p1 ≤ vHL; reason: above vHL nobody buys in period 1, yet equation (2) still lets period-2 anecdotes come from period 1 and be H with probability ξ1; with p1 > vHL allowed the result is false (α = 1, vH = 3, vL = 1, cH = 3, cL = 9/10 lies in region (ii) with Π* = 121/210, but p1 > vHL, ξ1 = 1, p2 = vHL, ξ2 = 0 earns 11/10)
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §4, p. 11 (unnumbered; the K = 1 case of Lemma 1, p. 10)

import Mathlib
import Definitions.Def_HuangYin_Policy_Feasible
import Definitions.Def_HuangYin_opaqueProfit

namespace HuangYin

/-- **Price reduction to the two candidates `vL` and `vHL`** (§4, p. 11; unnumbered, the `K = 1`
case of Lemma 1, p. 10).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), §4, p. 11: "According to Lemma 1, the optimal price in each period should be chosen
among the two candidates: vL and (vH−vL)/2 + vL."

Every feasible opaque policy (`ξ1, ξ2 ∈ [0,1]`, `p1 ≤ vHL`, `p2` arbitrary) is weakly beaten by an
opaque policy whose prices both lie in `{vL, vHL}`, with suitable offering probabilities in
`[0,1]`.

**Formalization Note.** The offering probabilities may change: at `p2 > vHL` nobody buys in
period 2, and the same `ξ2` at `p2 = vHL` can earn a negative margin. -/
theorem optimal_price_candidates (P : Params) :
    ∀ p1 p2 ξ1 ξ2 : ℝ, (Policy.opaque p1 p2 ξ1 ξ2).Feasible P →
      ∃ q1 ∈ ({P.vL, vHL P} : Set ℝ), ∃ q2 ∈ ({P.vL, vHL P} : Set ℝ),
        ∃ x1 ∈ Set.Icc (0 : ℝ) 1, ∃ x2 ∈ Set.Icc (0 : ℝ) 1,
          opaqueProfit P p1 p2 ξ1 ξ2 ≤ opaqueProfit P q1 q2 x1 x2 := by sorry

end HuangYin
