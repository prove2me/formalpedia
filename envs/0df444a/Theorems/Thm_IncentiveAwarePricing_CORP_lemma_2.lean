-- Prove2me | Theorems.Thm_IncentiveAwarePricing_CORP_lemma_2
-- name    : IncentiveAwarePricing.CORP.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:55.104534+00:00
-- url     : https://prove2.me/theorems/f6548012-6bcf-436b-86fb-0cc52044d6bc
-- title:
--   Lemma 2, p. 56 — |r⋆ − r| ≤ |⟨x, β − β̂⟩| for maximizers of y(1 − F(y − ⟨x, β⟩)) and y(1 − F(y − ⟨x, β̂⟩))
-- statement:
--   Let $f$ be a noise density on $[-B_n,B_n]$ with distribution function $F$ satisfying Assumption 1. Let $x,\beta,\hat\beta\in\mathbb R^d$ with $\langle x,\beta\rangle>-B_n$ and $\langle x,\hat\beta\rangle>-B_n$. If $r^\star$ maximizes $y\mapsto y(1-F(y-\langle x,\beta\rangle))$ and $r$ maximizes $y\mapsto y(1-F(y-\langle x,\hat\beta\rangle))$ over $y\in\mathbb R$, then
--   $$|r^\star-r|\le|\langle x,\beta-\hat\beta\rangle| .$$
--
--   So the reserve CORP posts in an exploitation period is off the benchmark reserve by at most the error in the estimated index (40).
--
--   **Formalization Note** The two hypotheses $\langle x,\beta\rangle>-B_n$, $\langle x,\hat\beta\rangle>-B_n$ are added: below $-B_n$ the objective vanishes on the whole half-line $[\theta+B_n,\infty)$ and a maximizer can be arbitrarily far away. The page's wrapper ("$t\in E_k$ with $\xi_t=1$, conditioned on $x_t$ and $\hat\beta_{ik}$") is dropped, since the inequality is deterministic.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, p. 56, Lemma 2, (40)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-- **Lemma 2** (Errors in Reserve Prices), p. 56, (40). If `r⋆` maximizes
`y (1 - F(y - ⟨x, β⟩))` and `r` maximizes `y (1 - F(y - ⟨x, β̂⟩))`, and both indices exceed
`-Bn`, then `|r⋆ - r| ≤ |⟨x, β - β̂⟩|`. -/
theorem lemma_2 (d : ℕ) (Bn : ℝ) (f : ℝ → ℝ)
    (hf : NoiseStanding Bn f) (hA1 : Assumption1 Bn f)
    (x β βhat : Ctx d) (hβ : -Bn < ⟪x, β⟫) (hβhat : -Bn < ⟪x, βhat⟫)
    (rStar r : ℝ) (hrStar : IsMaxOn (reserveObjective f ⟪x, β⟫) Set.univ rStar)
    (hr : IsMaxOn (reserveObjective f ⟪x, βhat⟫) Set.univ r) :
    |rStar - r| ≤ |⟪x, β - βhat⟫| := by sorry

end IncentiveAwarePricing.CORP
