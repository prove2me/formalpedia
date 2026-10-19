-- Prove2me | Theorems.Thm_IncentiveAwarePricing_CORP_proposition_3_1
-- name    : IncentiveAwarePricing.CORP.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:35.069816+00:00
-- url     : https://prove2.me/theorems/77aa0c86-e40e-4c1d-afa9-5ad2da791170
-- title:
--   Proposition 3.1, pp. 15–16 — reserves r⋆_i(x) = argmax_y y(1 − F(y − ⟨x, β_i⟩)) maximize the lazy second-price revenue against truthful buyers
-- statement:
--   Let $f$ be a noise density on $[-B_n,B_n]$ with distribution function $F$ satisfying Assumption 1, let $N\ge1$, let $x\in\mathbb R^d$ with $\|x\|\le1$ and let $\beta_1,\dots,\beta_N$ be preference vectors with $\|\beta_i\|\le B_p$. Buyers are truthful: buyer $i$ bids his valuation $v_i=\langle x,\beta_i\rangle+z_i$, the noises $z_i$ being independent with density $f$. For a reserve vector $r\in\mathbb R^N$ write
--   $$\mathrm{Rev}(r)=\mathbb E_z\Big[\sum_{i}p_i\Big]$$
--   for the expected revenue of the lazy second-price auction with reserves $r$. If, for every $i$, $r_i$ maximizes $y\mapsto y\,(1-F(y-\langle x,\beta_i\rangle))$ over $y\in\mathbb R$, then
--   $$\mathrm{Rev}(r')\le\mathrm{Rev}(r)\qquad\text{for every } r'\in\mathbb R^N.$$
--
--   This is the benchmark of the regret: the optimal reserve of buyer $i$ depends only on his own index $\langle x,\beta_i\rangle$, and the benchmark revenue (5) is the expected revenue of these reserves.
--
--   **Formalization Note** "Is given by" is formalized as optimality of every maximizer; uniqueness is not claimed, since for $\langle x,\beta_i\rangle\le -B_n$ every $y\ge\langle x,\beta_i\rangle+B_n$ is a maximizer. The optimization is pointwise in $x$, which is the same as optimizing a reserve map $x\mapsto r(x)$.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, pp. 15–16, Proposition 3.1, (4)–(5)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-- **Proposition 3.1** (Benchmark), pp. 15–16. Against truthful buyers, for a fixed feature
vector `x`, any reserve vector `r` with `r_i` a maximizer of `y (1 - F(y - ⟨x, β_i⟩))` for each
`i` maximizes the expected revenue of the lazy second-price auction over all reserve vectors. -/
theorem proposition_3_1 (N d : ℕ) (Bp Bn : ℝ) (f : ℝ → ℝ)
    (hN : 1 ≤ N) (hf : NoiseStanding Bn f) (hA1 : Assumption1 Bn f)
    (x : Ctx d) (hx : ‖x‖ ≤ 1) (β : Fin N → Ctx d) (hβ : ∀ i, ‖β i‖ ≤ Bp)
    (r : Fin N → ℝ) (hr : ∀ i, IsMaxOn (reserveObjective f ⟪x, β i⟫) Set.univ (r i)) :
    ∀ r' : Fin N → ℝ,
      ∫ z, lazyRevenue (values x β z) r' ∂(Measure.pi fun _ : Fin N => noiseLaw f) ≤
        ∫ z, lazyRevenue (values x β z) r ∂(Measure.pi fun _ : Fin N => noiseLaw f) := by sorry

end IncentiveAwarePricing.CORP
