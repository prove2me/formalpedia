-- Prove2me | Theorems.Thm_HuangYin_lemma_4
-- name    : HuangYin.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:47:17.768413+00:00
-- url     : https://prove2.me/theorems/f15288b6-7fd6-4d8b-a518-520b9fb27365
-- title:
--   Lemma 4 — the case $p_1=v_L$, $p_2=v_{HL}$ is dominated (corrected: $\xi_1=1$ or $\xi_1=0$)
-- statement:
--   Consider the prices $p_1=v_L$, $p_2=v_{HL}$.
--
--   1. For every $\xi_2\in[0,1]$, the best first-period probability is an endpoint: for all $x_1,x_2\in[0,1]$, $\Pi(x_1,x_2\mid v_L,v_{HL})\le\max\{\Pi(0,x_2\mid v_L,v_{HL}),\,\Pi(1,x_2\mid v_L,v_{HL})\}$.
--   2. With $\xi_1=1$ the case is dominated by $p_1=p_2=v_{HL}$: $\Pi(1,x_2\mid v_L,v_{HL})\le\Pi(1,x_2\mid v_{HL},v_{HL})$ for every $x_2\in[0,1]$.
--   3. With $\xi_1=0$ the case is dominated by $p_1=v_{HL}$, $p_2=v_L$: for every $x_2\in[0,1]$ there are $y_1,y_2\in[0,1]$ with $\Pi(0,x_2\mid v_L,v_{HL})\le\Pi(y_1,y_2\mid v_{HL},v_L)$.
--
--   Together these show that the price pair $(v_L,v_{HL})$ never needs to be considered.
--
--   Differences from the source:
--
--   - correction: (i) 'ξ1 = 1 or ξ2 = 0 is optimal' → (i) for each ξ2, the best ξ1 is 1 or 0; reason: false as printed: at α = 0, vH = 3, vL = 1, cH = 2, cL = 1 the profit is −ξ1 + ξ2 − ξ2², uniquely maximized at (0, 1/2), so no maximizer has ξ1 = 1 or ξ2 = 0; clauses (ii) 'If ξ1 = 1' and (iii) 'If ξ1 = 0' show that ξ1 = 0 was meant
--   - encoding: K anecdotes per customer and a prior belief ξ0 (p. 8), with ξ0 = 0 from p. 9 on and K = 1 in §4 → the estimate (ξ0 + anecdote)/(K + 1) with K = 1, ξ0 = 0 built into `estimate`; the purchasing fractions derived from rule (1) in `demand`; reason: §4 and the result fix K = 1 and the paper fixes ξ0 = 0; the derived fractions are Lemma 1's γ's for K = 1 (1 at vL, ξ at vHL, 0 above vHL), so no instance changes
--   - reading: 'this case is dominated by the case …' → pointwise in ξ2: for each ξ2 the other price case earns at least as much (with the same probabilities in (ii), with some probabilities in [0, 1] in (iii)); reason: the pointwise reading is the stronger one and is what the proof of Proposition 1 needs
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Lemma 4, p. 12

import Mathlib
import Definitions.Def_HuangYin_opaqueProfit
import Definitions.Def_HuangYin_vHL

namespace HuangYin

/-- **Lemma 4: the case `p1 = vL`, `p2 = vHL` is dominated** (p. 12), with the corrected clause (i).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), Lemma 4, p. 12.

At `p1 = vL`, `p2 = vHL`:
(i) for every `ξ2 ∈ [0,1]`, the best `ξ1 ∈ [0,1]` is `ξ1 = 1` or `ξ1 = 0`;
(ii) with `ξ1 = 1`, the policy is weakly beaten by `p1 = p2 = vHL` with the same `ξ1 = 1`, `ξ2`;
(iii) with `ξ1 = 0`, the policy is weakly beaten by some policy with `p1 = vHL`, `p2 = vL` and
offering probabilities in `[0,1]`.

**Formalization Note.** The printed (i) reads "ξ1 = 1 or ξ2 = 0 is optimal"; it is corrected to
"ξ1 = 1 or ξ1 = 0", the two cases that (ii) and (iii) treat. As printed it is false: at α = 0,
vH = 3, vL = 1, cH = 2, cL = 1 the profit is `−ξ1 + ξ2 − ξ2²`, uniquely maximized at
`(0, 1/2)`, with `ξ1 ≠ 1` and `ξ2 ≠ 0`. "Dominated" is read pointwise in `ξ2`. -/
theorem lemma_4 (P : Params) :
    (∀ x1 ∈ Set.Icc (0 : ℝ) 1, ∀ x2 ∈ Set.Icc (0 : ℝ) 1,
      opaqueProfit P P.vL (vHL P) x1 x2 ≤
        max (opaqueProfit P P.vL (vHL P) 0 x2) (opaqueProfit P P.vL (vHL P) 1 x2)) ∧
    (∀ x2 ∈ Set.Icc (0 : ℝ) 1,
      opaqueProfit P P.vL (vHL P) 1 x2 ≤ opaqueProfit P (vHL P) (vHL P) 1 x2) ∧
    (∀ x2 ∈ Set.Icc (0 : ℝ) 1, ∃ y1 ∈ Set.Icc (0 : ℝ) 1, ∃ y2 ∈ Set.Icc (0 : ℝ) 1,
      opaqueProfit P P.vL (vHL P) 0 x2 ≤ opaqueProfit P (vHL P) P.vL y1 y2) := by sorry

end HuangYin
