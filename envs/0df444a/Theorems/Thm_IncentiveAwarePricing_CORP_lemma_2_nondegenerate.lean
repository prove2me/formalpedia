-- Prove2me | Theorems.Thm_IncentiveAwarePricing_CORP_lemma_2_nondegenerate
-- name    : IncentiveAwarePricing.CORP.lemma_2_nondegenerate
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-22T04:27:45.968993+00:00
-- url     : https://prove2.me/theorems/4eced32c-428c-4497-845a-d51a1c81a176
-- title:
--   Lemma 2, p. 56 (with non-degenerate noise) — the optimal reserve is 1-Lipschitz in the index: |r⋆ − r| ≤ |⟨x, β − β̂⟩|
-- statement:
--   This is Lemma 2 of Golrezaei–Javanmard–Mirrokni (errors in reserve prices), with the non-degeneracy condition that the paper's proof uses implicitly.
--
--   Let $f$ be a noise density on $[-B_n,B_n]$ with distribution function $F$: $f$ is continuous on $[-B_n,B_n]$, vanishes outside it, and has mass one and mean zero. Assume $F$ and $1-F$ are log-concave on $[-B_n,B_n]$ (Assumption 1), and assume in addition that
--   $$F(z)<1\qquad\text{for all } z<B_n .$$
--   Let $x,\beta,\hat\beta\in\mathbb R^d$ with $\langle x,\beta\rangle>-B_n$ and $\langle x,\hat\beta\rangle>-B_n$. Let $r^\star$ maximize $y\mapsto y\,(1-F(y-\langle x,\beta\rangle))$ over $\mathbb R$, and let $r$ maximize $y\mapsto y\,(1-F(y-\langle x,\hat\beta\rangle))$. Then
--   $$|r^\star-r|\le|\langle x,\beta-\hat\beta\rangle| .$$
--
--   In words, the optimal reserve price $g(\theta)=\arg\max_y y(1-F(y-\theta))$ is a well-defined, $1$-Lipschitz function of the index $\theta$ on $(-B_n,\infty)$. In the regret analysis of CORP, this converts estimation error in the preference vectors into error in the posted reserves.
--
--   **Formalization Note.** The milestone statement `IncentiveAwarePricing.CORP.lemma_2` lacks the hypothesis $F(z)<1$ for $z<B_n$ and has been disproved. Without it, $F$ may reach $1$ strictly inside $(-B_n,B_n)$, and for $\theta$ close to $-B_n$ every $y\ge 0$ is a maximizer. The paper's footnote 20 (p. 70) asserts strict log-concavity of $y(1-F(y-\theta))$ for $y>0$, which presupposes $1-F>0$ on $[-B_n,B_n)$. The added hypothesis holds, for example, whenever $f>0$ on a left neighbourhood of $B_n$, and in particular for the uniform, truncated Laplace and truncated logistic noises the paper lists.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, p. 56, Lemma 2, eq. (40); proof Section 17.2, p. 85; footnote 20, p. 70

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-- **Lemma 2** (Errors in Reserve Prices), p. 56, (40), with the non-degeneracy hypothesis
`F(z) < 1` for `z < Bn` that the proof (p. 70, footnote 20; p. 85) uses implicitly. If `r⋆`
maximizes `y (1 - F(y - ⟨x, β⟩))` and `r` maximizes `y (1 - F(y - ⟨x, β̂⟩))`, and both indices
exceed `-Bn`, then `|r⋆ - r| ≤ |⟨x, β - β̂⟩|`. -/
theorem lemma_2_nondegenerate (d : ℕ) (Bn : ℝ) (f : ℝ → ℝ)
    (hf : NoiseStanding Bn f) (hA1 : Assumption1 Bn f)
    (hF : ∀ z, z < Bn → noiseCDF f z < 1)
    (x β βhat : Ctx d) (hβ : -Bn < ⟪x, β⟫) (hβhat : -Bn < ⟪x, βhat⟫)
    (rStar r : ℝ) (hrStar : IsMaxOn (reserveObjective f ⟪x, β⟫) Set.univ rStar)
    (hr : IsMaxOn (reserveObjective f ⟪x, βhat⟫) Set.univ r) :
    |rStar - r| ≤ |⟪x, β - βhat⟫| := by sorry

end IncentiveAwarePricing.CORP
