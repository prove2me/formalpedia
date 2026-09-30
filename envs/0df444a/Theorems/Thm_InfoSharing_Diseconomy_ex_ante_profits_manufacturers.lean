-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_ex_ante_profits_manufacturers
-- name    : InfoSharing.Diseconomy.ex_ante_profits_manufacturers
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:08:33.465214+00:00
-- url     : https://prove2.me/theorems/8779480c-8e60-4345-be22-d5d3a33432c4
-- title:
--   §4.2 — the manufacturers' ex ante profits
-- statement:
--   Let $(\theta, Y)$ be a signal model with parameters $\sigma, \beta$, let $\phi > 0$, $b > 0$, $c = c_d > 0$, and let $E$ be any pricing-equilibrium family with payoff table $M$. For each manufacturer $i$ with rival $j$:
--
--   $$M(UU, i) = \pi_M(0),\quad M(I_iU_j, j) = \pi_M^U(1),\quad M(I_iU_j, i) = \pi_M^I(1),\quad M(II, i) = \pi_M(2),$$
--
--   with the closed forms of §4.2.
--
--   These identities turn the contracting games into games over explicit rational functions of $c$ and $\phi$.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 252, §4.2

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
import Definitions.Def_InfoSharing_Shared_ClosedForms
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

/-- §4.2, p. 252 (with `c = c_d > 0`): in every pricing-equilibrium family the manufacturers'
ex ante profits are `π_M(0)`, `π_M^I(1)`, `π_M^U(1)` and `π_M(2)`. -/
theorem ex_ante_profits_manufacturers {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    let P := payoffTable μ θ Y a b c φ E
    (∀ i : Fin 2, P.M (fun _ => Status.uninformed) i = piM0 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (onlyInformed i) (other i) = piMU1 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (onlyInformed i) i = piMI1 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (fun _ => Status.informed) i = piM2 a b c φ σ β) := by sorry

end InfoSharing.Diseconomy
