-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_lemma_3_profit_orderings
-- name    : InfoSharing.Diseconomy.lemma_3_profit_orderings
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:14:56.294238+00:00
-- url     : https://prove2.me/theorems/ec5e8642-3eb3-4c8c-b766-c19dfeb0967c
-- title:
--   Lemma 3 — orderings of the ex ante profits under production diseconomy
-- statement:
--   Let $(\theta, Y)$ be a signal model with parameters $\sigma, \beta$, let $\phi > 0$, $b > 0$, $c = c_d > 0$, and let $E$ be any pricing-equilibrium family. Then, writing the ex ante profits in the paper's notation (the informed manufacturer at $n = 1$ may be either one):
--
--   1. $\pi_M(2) > \pi_M^I(1) > \pi_M(0) > \pi_M^U(1)$;
--   2. $\pi_R(0) > \pi_R(1) > \pi_R(2)$;
--   3. $$\pi_R(1) - \pi_R(2) > \pi_R(0) - \pi_R(1).$$
--
--   Information sharing benefits the informed manufacturer and hurts the retailer; these orderings drive every proposition of §5.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 259, Lemma 3

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

/-- Lemma 3, p. 259 (production diseconomy, profits of §4.2 with `c = c_d`), for the payoff
table of any pricing-equilibrium family and either manufacturer `i` as the informed one when
`n = 1`:
(a) `π_M(2) > π_M^I(1) > π_M(0) > π_M^U(1)`;
(b) `π_R(0) > π_R(1) > π_R(2)`;
(c) `π_R(1) − π_R(2) > π_R(0) − π_R(1)`. -/
theorem lemma_3_profit_orderings {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) (i : Fin 2) :
    let P := payoffTable μ θ Y a b c φ E
    (P.M (fun _ => Status.informed) i > P.M (onlyInformed i) i ∧
      P.M (onlyInformed i) i > P.M (fun _ => Status.uninformed) i ∧
      P.M (fun _ => Status.uninformed) i > P.M (onlyInformed i) (other i)) ∧
    (P.R (fun _ => Status.uninformed) > P.R (onlyInformed i) ∧
      P.R (onlyInformed i) > P.R (fun _ => Status.informed)) ∧
    P.R (onlyInformed i) - P.R (fun _ => Status.informed) >
      P.R (fun _ => Status.uninformed) - P.R (onlyInformed i) := by sorry

end InfoSharing.Diseconomy
