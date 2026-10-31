-- Prove2me | Theorems.Thm_MarketplaceScalability_proposition_1
-- name    : MarketplaceScalability.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:54:11.62588+00:00
-- url     : https://prove2.me/theorems/5966f2bd-1ce0-460a-9bcc-3217bfeb85f8
-- title:
--   Proposition 1 (corrected: D(0) = ∞ replaced by solvability of the first-order condition)
-- statement:
--   Consider the marketplace with high-type sellers only ($\mu=1$), and let $I_N$, $I_S$ be the investment levels at which the platform is indifferent about offering the service when sellers cannot and can scale. Then:
--
--   1. The maxima of $\pi_N$ and $\pi_S$ over prices $p>0$ are attained.
--   2. **(a)** The platform is less likely to provide the service in the scalable scenario:
--   $$
--   I_S\le I_N.
--   $$
--   3. If $I_S>0$, sellers use the platform service at every optimum of $\pi_S$.
--   4. The optimal price is unique in the non-scalable scenario, and unique among the prices at which sellers use the service in the scalable scenario.
--   5. **(b)** Let $p_S$ be an optimum of $\pi_S$ at which sellers use the platform service, and let $p_N$ be an optimum of $\pi_N$. Then
--   $$
--   p_S\le p_N,\qquad q(p_N)\le q(p_S),\qquad \pi(p_S)\le\pi(p_N).
--   $$
--
--   So the ability to scale lowers the platform's gain from offering the service. Where the service is offered anyway, the price and the profit are no higher and total output is no lower than when sellers cannot scale.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - reading: "decreases" and "increases" in (b) → ≤; reason: the proof says "weakly higher" (p.26), and strict inequalities are false: the instance D = 10 − q, α = 1/10, c̄ = 6, c = 1, c̲ = 1/2, f = 1, F = 33 has the same optimum in both scenarios, with I_S > 0
--   - reading: conditional on providing the service → sellers use the platform service at the scalable optimum; reason: this holds whenever I_S > 0 (a clause of the theorem); at I_S = 0 a price above p_s can be optimal with no seller using the service, and the comparison has no meaning there
--   - reading: the optimal platform price → uniqueness clauses; reason: the source's "the" presupposes uniqueness
--   - encoding: max over p, ties → prices in (0, ∞), sSup in I_N and I_S with attainment stated, q through invFunOn, ties to the platform; reason: positive prices are the only ones with a solution of the first-order condition; (4) and (6) print the ties this way
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, Proposition 1, p.10

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_IN
import Definitions.Def_MarketplaceScalability_Params_IS

namespace MarketplaceScalability

/-- **Proposition 1 (corrected: D(0) = ∞ replaced by solvability of the first-order condition).**
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, Proposition 1, p.10: "(a) The platform is less likely to provide the ancillary service in the
scalable scenario than the non-scalable scenario; i.e., IN ≥ IS. (b) Conditional on providing the
service, the optimal platform price decreases, total output increases, and the platform's profit
decreases in the scalable scenario relative to the non-scalable scenario."

For every `M : Model`:
1. the maxima in (5) and (7) are attained;
2. (a): `I_S ≤ I_N`;
3. if `I_S > 0`, sellers use the platform service at every optimum of `π_S`;
4. the optimal price is unique in each scenario (among prices at which sellers use the service in the
   scalable one);
5. (b): at optima `p_S` of `π_S`, where sellers use the service, and `p_N` of `π_N`, one has
   `p_S ≤ p_N`, `q(p_N) ≤ q(p_S)` and `π(p_S) ≤ π(p_N)`.

**Formalization Note**
* The demand conditions are corrected, see `Model`.
* "Decreases" and "increases" are weak: the proof says "weakly higher" (p.26), and strict inequalities are
  false (`Solutions/verification/MarketplaceScalability_sanity.lean`, `F = 33`).
* "Conditional on providing" is `usesPlatformS p_S`. It holds when `I_S > 0` (clause 3). At `I_S = 0` a price
  above `p_s` can be optimal for `π_S` with no seller using the service.
* The non-scalable side needs no such hypothesis, since every optimum of `π_N` is at most `c̄`.
* With `μ = 1`, total output is `q`. -/
theorem proposition_1 (M : Model) :
    (∃ p ∈ Set.Ioi 0, IsMaxOn M.piN (Set.Ioi 0) p) ∧
    (∃ p ∈ Set.Ioi 0, IsMaxOn M.piS (Set.Ioi 0) p) ∧
    M.IS ≤ M.IN ∧
    (0 < M.IS → ∀ p ∈ Set.Ioi 0, IsMaxOn M.piS (Set.Ioi 0) p → M.usesPlatformS p) ∧
    (∀ p ∈ Set.Ioi 0, ∀ p' ∈ Set.Ioi 0,
      IsMaxOn M.piN (Set.Ioi 0) p → IsMaxOn M.piN (Set.Ioi 0) p' → p = p') ∧
    (∀ p ∈ Set.Ioi 0, ∀ p' ∈ Set.Ioi 0,
      IsMaxOn M.piS (Set.Ioi 0) p → M.usesPlatformS p →
      IsMaxOn M.piS (Set.Ioi 0) p' → M.usesPlatformS p' → p = p') ∧
    (∀ pS ∈ Set.Ioi 0, ∀ pN ∈ Set.Ioi 0,
      IsMaxOn M.piS (Set.Ioi 0) pS → M.usesPlatformS pS → IsMaxOn M.piN (Set.Ioi 0) pN →
      pS ≤ pN ∧ M.q pN ≤ M.q pS ∧ M.pi pS ≤ M.pi pN) := by sorry

end MarketplaceScalability
