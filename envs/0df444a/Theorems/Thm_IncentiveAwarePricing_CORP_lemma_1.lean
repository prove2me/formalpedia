-- Prove2me | Theorems.Thm_IncentiveAwarePricing_CORP_lemma_1
-- name    : IncentiveAwarePricing.CORP.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:48.61367+00:00
-- url     : https://prove2.me/theorems/56f19f56-2f2c-4863-8cf8-b19f43f2bf08
-- title:
--   Lemma 1, p. 56 — W_i′(r⋆_i) = 0 and |W_i″| ≤ c, for W_i(r) = E[max{v⁺_{−i}, r} I(v_i ≥ max{v⁺_{−i}, r}) | x]
-- statement:
--   Let $f$ be a noise density on $[-B_n,B_n]$ satisfying Assumption 1 which is moreover continuously differentiable on $\mathbb R$, and let $N\ge1$. For a feature vector $x$ with $\|x\|\le1$, preference vectors $\|\beta_j\|\le B_p$ and truthful valuations $v_j=\langle x,\beta_j\rangle+z_j$, define for buyer $i$
--   $$W_i(r)=\mathbb E\Big[\max\{v^+_{-i},r\}\,\mathbb I\big(v_i\ge\max\{v^+_{-i},r\}\big)\Big],\qquad v^+_{-i}=\max_{j\ne i}v_j ,$$
--   the expectation being over the noises (so it is conditional on $x$), and with $\max\{v^+_{-i},r\}=r$ when $N=1$. Then there is a constant $c>0$, depending only on $N,B_p,B_n,f$, such that for every such $x,\beta,i$ and every maximizer $r^\star_i$ of $y\mapsto y(1-F(y-\langle x,\beta_i\rangle))$: $W_i$ is differentiable on $\mathbb R$, its derivative satisfies $W_i'(r^\star_i)=0$, and $W_i'$ is differentiable on $\mathbb R$ with
--   $$|W_i''(r)|\le c\qquad\text{for all } r\in\mathbb R .$$
--
--   In the regret analysis this gives a second-order bound on the revenue lost by a reserve $r_{it}$ near $r^\star_{it}$ (39), (41).
--
--   **Formalization Note** (38) prints $v^-_t$; the paper's own restatement on p. 69 has $v^+_{-it}$, which is what is encoded. The hypothesis that $f$ is $C^1$ on $\mathbb R$ (so $f(\pm B_n)=0$) is added: the proof on p. 84 differentiates $f$, and if $f$ jumps at $\pm B_n$ then $W_i''$ does not exist there. The constant depends on $N$ (through the density of a maximum of $N-1$ valuations), as the proof's does. The page bounds $W''$ for $r$ between $r_{it}$ and $r^\star_{it}$; the bound is stated for all $r$, which covers every such $r$. Derivatives are asserted with `HasDerivAt`, not `deriv`.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, p. 56, Lemma 1; (38) p. 55 in the form of p. 69; proof pp. 84–85

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-- **Lemma 1** (Property of Function `W_it`), p. 56. With `W_i(r) = E[max{v⁺_{-i}, r} ·
I(v_i ≥ max{v⁺_{-i}, r}) | x]` ((38), in the form of p. 69), `W_i'(r⋆_i) = 0` at every maximizer
`r⋆_i` of (4), and `|W_i''| ≤ c` everywhere, for a constant `c > 0` that depends only on
`N, Bp, Bn, f`. Here `max{v⁺_{-i}, r} = thresh v (fun _ => r) i` (equal to `r` when `N = 1`). -/
theorem lemma_1 (N : ℕ) (Bp Bn : ℝ) (f : ℝ → ℝ)
    (hf : NoiseStanding Bn f) (hA1 : Assumption1 Bn f) (hC1 : ContDiff ℝ 1 f) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (x : Ctx d) (β : Fin N → Ctx d) (i : Fin N), ‖x‖ ≤ 1 → (∀ j, ‖β j‖ ≤ Bp) →
      ∀ rStar : ℝ, IsMaxOn (reserveObjective f ⟪x, β i⟫) Set.univ rStar →
        let W : ℝ → ℝ := fun r =>
          ∫ z, (if thresh (values x β z) (fun _ => r) i ≤ values x β z i
            then thresh (values x β z) (fun _ => r) i else 0)
            ∂(Measure.pi fun _ : Fin N => noiseLaw f)
        ∃ W' : ℝ → ℝ, (∀ r, HasDerivAt W (W' r) r) ∧ W' rStar = 0 ∧
          ∀ r : ℝ, ∃ w₂ : ℝ, HasDerivAt W' w₂ r ∧ |w₂| ≤ c := by sorry

end IncentiveAwarePricing.CORP
