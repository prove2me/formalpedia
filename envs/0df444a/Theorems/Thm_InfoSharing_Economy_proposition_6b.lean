-- Prove2me | Theorems.Thm_InfoSharing_Economy_proposition_6b
-- name    : InfoSharing.Economy.proposition_6b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T00:11:59.276818+00:00
-- url     : https://prove2.me/theorems/632e947c-4ecf-42fd-8b2e-0cbe53f7760d
-- title:
--   Proposition 6(b) — equilibrium information sharing without side payment (production economy)
-- statement:
--   For every $\phi > 0$ there is a threshold $c_e^N \in (1/(1+\phi), 2/(1+\phi))$, depending only on $\phi$, such that the following holds. Let $0 < c_e < 2/(1+\phi)$, put $c = -c_e$, and let $a, b$ be reals. Let $(\theta, Y)$ satisfy the signal model with variance $\sigma^2$ and weight $\beta = \beta(t,\sigma)$, let $E$ be any family of pricing equilibria with payoff table $P$, and let $n_e^N$ be the number of informed manufacturers when the retailer chooses the statuses freely, without payment. Then
--
--   $$n_e^N = \begin{cases} 0 & c_e < 1/(1+\phi), \\ 2 & 1/(1+\phi) \le c_e < c_e^N, \\ 1 & c_e^N \le c_e < 2/(1+\phi), \end{cases}$$
--
--   in the two-clause form: on each region the stated value of $n$ is attained by some outcome, and on the interior of the region it is the only value attained (at a boundary point the retailer is indifferent between outcomes).
--
--   A retailer may thus have an incentive to share information for free, which production diseconomy never gives her.
--
--   **Formalization Note** The production economy model takes $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ (the Assumption of p. 251). The ex ante profits are those of an equilibrium of the pricing game on the signal model, not the closed forms: the closed forms are the content of the §4.2 milestones. The production cost is the uncapped quadratic $bq - c_e q^2$ (the paper's cap at $\bar q = b/(2c_e)$ is assumed never to bind, footnote 11, p. 251). **Correction of the paper.** The single value $c_e^* = \frac{2+3\phi}{(1+2\phi)(1+\phi)}$ (which lies in $(1/(1+\phi), 2/(1+\phi))$) is excluded: there the slope $\phi(1+(1+\phi)c)/[(1+\phi)(2+(1+\phi)c)]$ of the best response (2) equals $-1$, so the pricing stage has a continuum of equilibria with different ex ante profits, and Lemma 1's uniqueness claim, on which the payoff table rests, fails.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 255, Proposition 6(b)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
import Definitions.Def_InfoSharing_Economy_NoContractOptN
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- **Proposition 6(b)** (Shang, Ha & Tong 2016, p. 255), production economy (`c = −c_e`) under
the Assumption `c_e < 2/(1+φ)`: without information contracting (the retailer chooses the
information statuses freely, with no payment), the equilibrium number `n_e^N` of informed
manufacturers, with a threshold `c_e^N` that depends only on `φ`. `NoContractOptN P` is the set
of values of `n` over all retailer-optimal status profiles; on each region `n` is attained, and it
is the only value in the region's interior.

**Correction.** The value `c_e = (2+3φ)/((1+2φ)(1+φ))` is excluded: there the best-response
slope in (2) is `−1`, the pricing stage has a continuum of equilibria with different ex ante
profits, and Lemma 1's uniqueness (on which the paper's payoff table rests) fails. -/
theorem proposition_6b :
    ∀ φ : ℝ, 0 < φ → ∃ cN : ℝ, 1 / (1 + φ) < cN ∧ cN < 2 / (1 + φ) ∧
    ∀ (ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      c = -ce → 0 < ce → ce < 2 / (1 + φ) → ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) →
      IsSignalModel μ θ Y σ β →
      IsPricingEqFamily μ θ Y a b c φ β E →
      let P := payoffTable μ θ Y a b c φ E
      ((ce < 1 / (1 + φ) → NoContractOptN P = {0}) ∧
         (1 / (1 + φ) ≤ ce → ce < cN → 2 ∈ NoContractOptN P) ∧
         (1 / (1 + φ) < ce → ce < cN → NoContractOptN P = {2}) ∧
         (cN ≤ ce → 1 ∈ NoContractOptN P) ∧
         (cN < ce → NoContractOptN P = {1})) := by sorry

end InfoSharing.Economy
