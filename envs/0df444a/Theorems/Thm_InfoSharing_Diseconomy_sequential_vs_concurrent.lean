-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_sequential_vs_concurrent
-- name    : InfoSharing.Diseconomy.sequential_vs_concurrent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:34:51.265987+00:00
-- url     : https://prove2.me/theorems/42744aa9-514e-4643-aa89-3afe8307bb6e
-- title:
--   Proposition 4(d) — under production diseconomy the retailer earns more under sequential, the manufacturers under concurrent information contracting
-- statement:
--   Let $(\theta, Y)$ be a signal model with parameters $\sigma, \beta$, and let $\phi > 0$, $b > 0$, $c = c_d > 0$. Then the pricing game has an equilibrium family, and for every pricing-equilibrium family:
--
--   1. concurrent contracting has an outcome, and sequential contracting has a subgame-perfect equilibrium for either first manufacturer $k$;
--   2. for every concurrent outcome $(T, X)$, every $k$ and every SPE $s$ with first mover $k$,
--
--   $$\Pi_R^C \le \Pi_R^S \quad\text{and}\quad \Pi_M^S \le \Pi_M^C,$$
--
--   where $\Pi_R$ is the retailer's profit after the side payments and $\Pi_M$ the manufacturers' total profit net of them;
--   3. if moreover $c_d > (\sqrt2 - 1)/(1+\phi)$, both inequalities are strict.
--
--   The retailer prefers the protocol in which she can exploit the manufacturers' competition for information; the supply chain's manufacturers prefer the one that treats them alike.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$. The paper says "higher". Below $(\sqrt2-1)/(1+\phi) = c_d^{S1}$ neither protocol sells information and all profits coincide, and at $c_d^{S1}$ an SPE may still sell nothing, so "higher" is stated as $\ge$ everywhere and $>$ strictly above $c_d^{S1}$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 254, Proposition 4(d)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Diseconomy_IsConcurrentOutcome
import Definitions.Def_InfoSharing_Shared_IsSequentialSPE
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

/-- Proposition 4(d), p. 254 (production diseconomy): the retailer's profit is higher under
sequential information contracting, whereas the total profit of the manufacturers is higher
under concurrent information contracting.

The pricing stage has an equilibrium family; for every such family both contracting games have
outcomes; every concurrent outcome and every SPE of the sequential game (either first mover)
compare weakly as stated, and strictly when `c > (√2 − 1)/(1 + φ)` (below it neither protocol
sells information and all profits coincide). -/
theorem sequential_vs_concurrent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) :
    (∃ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E) ∧
    ∀ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E →
      let P := payoffTable μ θ Y a b c φ E
      (∃ (T : ℝ) (X : Fin 2 → Status), IsConcurrentOutcome P T X) ∧
      (∀ k : Fin 2, ∃ s : SeqStrategy, IsSequentialSPE P k s) ∧
      ∀ (T : ℝ) (X : Fin 2 → Status) (k : Fin 2) (s : SeqStrategy),
        IsConcurrentOutcome P T X → IsSequentialSPE P k s →
          concRetailer P T X ≤ seqRetailer P k s ∧
          seqManufacturersTotal P k s ≤ concManufacturersTotal P T X ∧
          ((Real.sqrt 2 - 1) / (1 + φ) < c →
            concRetailer P T X < seqRetailer P k s ∧
            seqManufacturersTotal P k s < concManufacturersTotal P T X) := by sorry

end InfoSharing.Diseconomy
