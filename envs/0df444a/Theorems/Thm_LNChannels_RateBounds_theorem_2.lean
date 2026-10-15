-- Prove2me | Theorems.Thm_LNChannels_RateBounds_theorem_2
-- name    : LNChannels.RateBounds.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:35.531227+00:00
-- url     : https://prove2.me/theorems/dee1514f-7953-4758-b3cf-8d69af696218
-- title:
--   Theorem 2 (Bounds on Payment Rates), pp. 6–7 — a channel beats on-chain settlement only if the on-chain fee exceeds an explicit threshold
-- statement:
--   Two nodes exchange payments: a payment from one node to the other arrives at the jumps of a Poisson process. Capital is discounted at the rate $r>0$, resetting a channel costs $B>0$, and an on-chain transaction costs $C\in\mathbb R$. Settling a stream of rate $\lambda$ on chain costs $\lambda C/r$ (Lemma 1).
--
--   1. **Unidirectional channel.** Let $\lambda>0$. If for some real size $m>0$
--   $$m+B\Big(\big(\tfrac{r+\lambda}{\lambda}\big)^m-1\Big)^{-1}<\frac{\lambda C}{r},$$
--   then
--   $$C>\log\Big(1+B\log\big(1+\tfrac r\lambda\big)\Big).$$
--   2. **Symmetric bidirectional channel.** Let both nodes pay at rate $\lambda>0$ and let $\kappa=\log\dfrac{r+2\lambda+\sqrt{r(4\lambda+r)}}{2\lambda}$. If for some real sizes $l_1,l_2>0$ the cost (3) satisfies $c^{l_1,l_2}(\lambda,\lambda)<2C\lambda/r$, then
--   $$C>3\Big(\frac{B\kappa^4}{4}\Big)^{1/3}-\frac B{12}\kappa^2 .$$
--
--   In words: a payment channel is worth opening only when on-chain fees are high, reset costs low, payment rates high, or interest rates low. The thresholds are $Br/\lambda+o(r)$ and $3(Br^2/(4\lambda^2))^{1/3}-Br/(12\lambda)+o(r)$ as $r\to0$.
--
--   **Formalization Note** The channel costs are the closed forms (1) and (3) of Theorem 1 for real sizes (`uniCost`, `biCost`, real powers), as the proof minimizes over real sizes; the hypotheses quantify over real sizes, which makes the theorem stronger than the same statement for natural sizes. "Costs less" is strict and existential in the size. The on-chain costs $\lambda C/r$ and $2C\lambda/r$ are written out. No sign is imposed on $C$. The "$=\dots+o(r)$" parts of (5) and (6) are a separate milestone and are not part of this statement.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, pp. 6–7 (PDF pp. 7–8), Theorem 2, eqs. (5)–(6)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- Theorem 2 (Bounds on Payment Rates), pp. 6–7. For `B, r, λ > 0` and any on-chain fee `C`:
(i) if a unidirectional channel with rate `λ` of some real size `m > 0` costs strictly less than
on-chain settlement `λC/r`, then `C > log(1 + B log(1 + r/λ))`;
(ii) if a symmetric bidirectional channel with rates `λ` and some real sizes `l₁, l₂ > 0` costs
strictly less than on-chain settlement `2Cλ/r`, then `C > 3(Bκ⁴/4)^{1/3} − (B/12)κ²` with
`κ = log((r + 2λ + √(r(4λ + r)))/(2λ))`. -/
theorem theorem_2 (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B) :
    ((∃ m : ℝ, 0 < m ∧ LNChannels.Exact.uniCost lam r B m < lam * C / r) →
        Real.log (1 + B * Real.log (1 + r / lam)) < C) ∧
      (let κ := Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam));
        (∃ l₁ l₂ : ℝ, 0 < l₁ ∧ 0 < l₂ ∧ biCost lam lam r B l₁ l₂ < 2 * C * lam / r) →
          3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * κ ^ 2 < C) := by sorry

end LNChannels.RateBounds
