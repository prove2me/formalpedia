-- Prove2me | Theorems.Thm_LNChannels_RateBounds_theorem_2_i
-- name    : LNChannels.RateBounds.theorem_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:51.150094+00:00
-- url     : https://prove2.me/theorems/5e326eac-7e16-490e-8b96-8cab6bf33e5c
-- title:
--   Theorem 2(i), p. 6 — a unidirectional channel beats on-chain settlement only if $C>\log(1+B\log(1+r/\lambda))$
-- statement:
--   Let $\lambda>0$ be the payment rate, $r>0$ the discount rate, $B>0$ the cost of resetting a channel and $C\in\mathbb R$ the cost of an on-chain transaction. Suppose a unidirectional channel with rate $\lambda$ costs strictly less than on-chain settlement for some size, that is, there is a real $m>0$ with
--   $$m+B\Big(\big(\tfrac{r+\lambda}{\lambda}\big)^m-1\Big)^{-1}<\frac{\lambda C}{r}.$$
--   Then
--   $$C>\log\Big(1+B\log\big(1+\tfrac r\lambda\big)\Big).$$
--
--   Equivalently, if the on-chain fee is at most $\log(1+B\log(1+r/\lambda))$ (which is $Br/\lambda+o(r)$ for small $r$), then for every channel size on-chain settlement is at least as cheap: low payment rates do not justify a channel.
--
--   **Formalization Note** The channel cost is the closed form (1) for a real size $m$ (`uniCost`), and the on-chain cost $\lambda C/r$ is that of Lemma 1, written out explicitly. The hypothesis quantifies over real sizes, so the theorem implies the same statement for natural sizes. The asymptotic identity "$=Br/\lambda+o(r)$" of (5) is a separate milestone, not part of this statement.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 6 (PDF p. 7), Theorem 2(i), eq. (5); proof p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- Theorem 2(i), p. 6: if a unidirectional channel with rate `λ` of some size `m > 0` costs
strictly less than on-chain settlement (`λC/r`, Lemma 1), then `C > log(1 + B log(1 + r/λ))`. -/
theorem theorem_2_i (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B) :
    (∃ m : ℝ, 0 < m ∧ LNChannels.Exact.uniCost lam r B m < lam * C / r) →
      Real.log (1 + B * Real.log (1 + r / lam)) < C := by sorry

end LNChannels.RateBounds
