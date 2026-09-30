-- Prove2me | Theorems.Thm_InfoSharing_Economy_sequential_vs_concurrent
-- name    : InfoSharing.Economy.sequential_vs_concurrent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T00:24:49.943369+00:00
-- url     : https://prove2.me/theorems/275b80c4-4ec2-49d1-b96b-65c5e42c8df2
-- title:
--   Proposition 8(d) — under production economy the retailer earns weakly more under sequential, the manufacturers under concurrent information contracting
-- statement:
--   For every $\phi > 0$ there are two values $c_1, c_2$, depending only on $\phi$, such that the following holds. Let $0 < c_e < 2/(1+\phi)$, put $c = -c_e$, and let $a, b$ be reals. Let $(\theta, Y)$ satisfy the signal model with variance $\sigma^2$ and weight $\beta = \beta(t,\sigma)$. Then the pricing game has a family of pricing equilibria, and for every such family $E$ with payoff table $P$:
--
--   1. a concurrent outcome exists, and for each first mover $k$ a subgame-perfect equilibrium of sequential contracting exists;
--   2. for every concurrent outcome $(T, X)$, every first mover $k$ and every SPE $s$,
--
--   $$\Pi_R^C(T, X) \le \Pi_R^S(k, s),$$
--
--   where $\Pi_R$ is the retailer's profit after the side payments;
--   3. if moreover $c_e \notin \{c_1, c_2\}$, then for the same objects
--
--   $$\Pi_M^S(k, s) \le \Pi_M^C(T, X),$$
--
--   where $\Pi_M$ is the manufacturers' total profit net of the side payments.
--
--   The common retailer prefers sequential contracting because it lets her charge a higher fee for the information, at the manufacturers' expense.
--
--   **Formalization Note** The production economy model takes $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ (the Assumption of p. 251). The ex ante profits are those of an equilibrium of the pricing game on the signal model, not the closed forms: the closed forms are the content of the §4.2 milestones. The production cost is the uncapped quadratic $bq - c_e q^2$ (the paper's cap at $\bar q = b/(2c_e)$ is assumed never to bind, footnote 11, p. 251). The paper says "higher"; the comparison is stated weakly because both sides coincide on intervals of positive length (for instance for $c_e < 1/(1+\phi)$, where no information is sold). The two excepted values are the thresholds $c_e^C$, $c_e^S$ of Proposition 7: there the retailer is indifferent between outcomes that give the manufacturers different totals, and pairing the less favourable concurrent outcome with the more favourable SPE reverses the manufacturers' comparison. **Correction of the paper.** The single value $c_e^* = \frac{2+3\phi}{(1+2\phi)(1+\phi)}$ (which lies in $(1/(1+\phi), 2/(1+\phi))$) is excluded from the clauses about every family of pricing equilibria (existence of a family is asserted for every $c_e$): there the slope $\phi(1+(1+\phi)c)/[(1+\phi)(2+(1+\phi)c)]$ of the best response (2) equals $-1$, so the pricing stage has a continuum of equilibria with different ex ante profits, and Lemma 1's uniqueness claim, on which the payoff table rests, fails.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 256, Proposition 8(d)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
import Definitions.Def_InfoSharing_Economy_IsConcurrentOutcome
import Definitions.Def_InfoSharing_Shared_IsSequentialSPE
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- **Proposition 8(d)** (Shang, Ha & Tong 2016, p. 256), production economy (`c = −c_e`) under
the Assumption `c_e < 2/(1+φ)` (p. 251): the retailer earns weakly more under sequential than
under concurrent information contracting, and the manufacturers' total profit (net of the side
payments) is weakly higher under concurrent contracting.

The pricing stage has an equilibrium family; for every such family, concurrent outcomes and
sequential SPEs (for either first mover `k`) exist; the retailer comparison holds for every
concurrent outcome and every SPE; the manufacturers' comparison holds for every concurrent
outcome and every SPE except at (at most) two values `c₁`, `c₂` of `c_e` that depend only on `φ`
(the thresholds `c_e^C`, `c_e^S` of Proposition 7, where the retailer is indifferent between two
outcomes that give the manufacturers different totals).

**Correction.** The value `c_e = (2+3φ)/((1+2φ)(1+φ))` is excluded from the clauses about
every pricing family (existence of a family is asserted for all `c_e`): there the best-response
slope in (2) is `−1`, the pricing stage has a continuum of equilibria with different ex ante
profits, and Lemma 1's uniqueness (on which the paper's payoff table rests) fails. -/
theorem sequential_vs_concurrent :
    ∀ φ : ℝ, 0 < φ → ∃ c₁ c₂ : ℝ,
    ∀ (ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ),
      c = -ce → 0 < ce → ce < 2 / (1 + φ) → IsSignalModel μ θ Y σ β →
      (∃ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E) ∧
      (ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) →
      ∀ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E →
        let P := payoffTable μ θ Y a b c φ E
        (∃ (T : ℝ) (X : Fin 2 → Status), IsConcurrentOutcome P T X) ∧
        (∀ k : Fin 2, ∃ s : SeqStrategy, IsSequentialSPE P k s) ∧
        (∀ (T : ℝ) (X : Fin 2 → Status) (k : Fin 2) (s : SeqStrategy),
          IsConcurrentOutcome P T X → IsSequentialSPE P k s →
            concRetailer P T X ≤ seqRetailer P k s) ∧
        (ce ≠ c₁ → ce ≠ c₂ →
          ∀ (T : ℝ) (X : Fin 2 → Status) (k : Fin 2) (s : SeqStrategy),
            IsConcurrentOutcome P T X → IsSequentialSPE P k s →
              seqManufacturersTotal P k s ≤ concManufacturersTotal P T X)) := by sorry

end InfoSharing.Economy
