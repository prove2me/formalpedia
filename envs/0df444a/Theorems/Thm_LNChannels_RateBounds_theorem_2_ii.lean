-- Prove2me | Theorems.Thm_LNChannels_RateBounds_theorem_2_ii
-- name    : LNChannels.RateBounds.theorem_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:59.436286+00:00
-- url     : https://prove2.me/theorems/2909d9d6-703b-41d2-a8b8-4e5d3a10708f
-- title:
--   Theorem 2(ii), p. 7 — a symmetric bidirectional channel beats on-chain settlement only if $C>3(B\kappa^4/4)^{1/3}-(B/12)\kappa^2$
-- statement:
--   Let $\lambda>0$ be the common payment rate of both nodes, $r>0$ the discount rate, $B>0$ the reset cost and $C\in\mathbb R$ the cost of an on-chain transaction, and let
--   $$\kappa=\log\frac{r+2\lambda+\sqrt{r(4\lambda+r)}}{2\lambda}.$$
--   Suppose a symmetric bidirectional channel with rates $\lambda$ costs strictly less than settling both streams on chain for some sizes, that is, there are real $l_1,l_2>0$ with $c^{l_1,l_2}(\lambda,\lambda)<2C\lambda/r$, where $c^{l_1,l_2}$ is the cost (3). Then
--   $$C>3\Big(\frac{B\kappa^4}{4}\Big)^{1/3}-\frac B{12}\kappa^2 .$$
--
--   Equivalently, if the on-chain fee is at most this threshold (which is $3(Br^2/(4\lambda^2))^{1/3}-Br/(12\lambda)+o(r)$ for small $r$), then for all sizes settling both streams on chain is at least as cheap as the symmetric channel.
--
--   **Formalization Note** The channel cost is the closed form `biCost` of (3) at $\lambda_1=\lambda_2=\lambda$ for real sizes; $2C\lambda/r$ is the on-chain cost of two streams of rate $\lambda$ (Lemma 1), written out explicitly. The asymptotic identity in (6) is a separate milestone, not part of this statement. The proof's sentence "positive if and only if $C\le\dots$" should read "$<$" (p. 12); the strict conclusion holds because (22) is strict.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 7 (PDF p. 8), Theorem 2(ii), eq. (6); proof pp. 11–12 (PDF pp. 12–13)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- Theorem 2(ii), p. 7: if a symmetric bidirectional channel with rates `λ` and some real sizes
`l₁, l₂ > 0` costs strictly less than on-chain settlement of both streams (`2Cλ/r`), then
`C > 3(Bκ⁴/4)^{1/3} − (B/12)κ²` with `κ = log((r + 2λ + √(r(4λ + r)))/(2λ))`. -/
theorem theorem_2_ii (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B) :
    let κ := Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam));
    (∃ l₁ l₂ : ℝ, 0 < l₁ ∧ 0 < l₂ ∧ biCost lam lam r B l₁ l₂ < 2 * C * lam / r) →
      3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * κ ^ 2 < C := by sorry

end LNChannels.RateBounds
