-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_proposition_6_7
-- name    : InvMarketMaking.LOB.proposition_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:12.086171+00:00
-- url     : https://prove2.me/theorems/bc14d916-55a1-4cf7-ac56-72d4b9ec3ea8
-- title:
--   Proposition 6.7 — on the active sets the LOB averages of $\chi^{\mathrm{sell}},\chi^{\mathrm{buy}}$ equal $\widehat F_t,\widehat S_t$
-- statement:
--   For valuations $V^{\mathrm{sell}}_\tau,V^{\mathrm{buy}}_\tau$ and posted prices $B_\tau,A_\tau$ define
--   $$
--   \chi^{\mathrm{sell}}_\tau(b)=\mathbb I(\max\{V^{\mathrm{sell}}_\tau,B_\tau\}\le b),\qquad \chi^{\mathrm{buy}}_\tau(a)=\mathbb I(\min\{V^{\mathrm{buy}}_\tau,A_\tau\}\ge a).
--   $$
--   If $B_\tau\le b$ for every $\tau\le t$ (in particular if $b\in\mathcal B_t=\bigcap_{\tau\le t}[B_\tau,1]$), then
--   $$
--   \frac1t\sum_{\tau=1}^t\chi^{\mathrm{sell}}_\tau(b)=\widehat F_t(b)=\frac1t\sum_{\tau=1}^t\mathbb I(V^{\mathrm{sell}}_\tau\le b),
--   $$
--   and if $a\le A_\tau$ for every $\tau\le t$ (in particular if $a\in\mathcal A_t=\bigcap_{\tau\le t}[0,A_\tau]$), then
--   $$
--   \frac1t\sum_{\tau=1}^t\chi^{\mathrm{buy}}_\tau(a)=\widehat S_t(a)=\frac1t\sum_{\tau=1}^t\mathbb I(V^{\mathrm{buy}}_\tau\ge a).
--   $$
--   Under limit-order-book feedback the maker observes $\max\{V^{\mathrm{sell}}_\tau,B_\tau\}$ and $\min\{V^{\mathrm{buy}}_\tau,A_\tau\}$, so on prices that stayed inside all past spreads it can compute the full-feedback estimators exactly.
--
--   Differences from the source:
--   - generalization: b, a ∈ [0, 1], t ∈ [T], b ∈ B_t = ∩_{τ≤t}[B_τ, 1], a ∈ A_t = ∩_{τ≤t}[0, A_τ], for the algorithm's prices → any real b, a, any t, any real valuation and price sequences, under B_τ ≤ b (resp. a ≤ A_τ) for τ ≤ t; reason: the identity uses only B_τ ≤ b (resp. a ≤ A_τ); membership in B_t, A_t and the algorithm's prices are special cases
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Proposition 6.7, Eqs. (17)–(19), p. 36

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_lobRound

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Proposition 6.7** (Maran, Restelli, Stradi, arXiv:2610.24562v1, p. 36). With
`χ^sell_τ(b) = I(max{V^sell_τ, B_τ} ≤ b)` and `χ^buy_τ(a) = I(min{V^buy_τ, A_τ} ≥ a)` (Eq. (17)):
if `b ∈ ℬ_t = ⋂_{τ ≤ t} [B_τ, 1]`, then `(1/t) Σ_{τ=1}^t χ^sell_τ(b) = F̂_t(b)` (Eq. (18)), and if
`a ∈ 𝒜_t = ⋂_{τ ≤ t} [0, A_τ]`, then `(1/t) Σ_{τ=1}^t χ^buy_τ(a) = Ŝ_t(a)` (Eq. (19)), where
`F̂_t, Ŝ_t` are the full-feedback estimators of Eq. (12).

**Formalization Note** Stated pathwise for arbitrary real sequences of valuations `vs, vb` and of
posted prices `bid, ask`, every `t` and every real `b, a`; the hypothesis keeps only the part
`B_τ ≤ b` (resp. `a ≤ A_τ`) of `b ∈ ℬ_t` (resp. `a ∈ 𝒜_t`) that the identity needs. At `t = 0`
both sides are `0`. -/
theorem proposition_6_7 (vs vb bid ask : ℕ → ℝ) (t : ℕ) :
    (∀ b : ℝ, (∀ τ ∈ Finset.Icc 1 t, bid τ ≤ b) →
      estSellOf vs bid t b = (∑ τ ∈ Finset.Icc 1 t, if vs τ ≤ b then (1 : ℝ) else 0) / t) ∧
    (∀ a : ℝ, (∀ τ ∈ Finset.Icc 1 t, a ≤ ask τ) →
      estBuyOf vb ask t a = (∑ τ ∈ Finset.Icc 1 t, if a ≤ vb τ then (1 : ℝ) else 0) / t) := by sorry

end InvMarketMaking.LOB
