-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_ex_ante_profits_retailer
-- name    : InfoSharing.Diseconomy.ex_ante_profits_retailer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:12:19.416964+00:00
-- url     : https://prove2.me/theorems/92c2f650-3fff-4033-a7d1-9a21abde70d4
-- title:
--   §4.2 — the retailer's ex ante profits
-- statement:
--   Under the hypotheses of the manufacturers' §4.2 identities, the retailer's ex ante profits in any pricing-equilibrium family are
--
--   $$R(UU) = \pi_R(0),\qquad R(I_iU_j) = \pi_R(1)\ \ (i = 1, 2),\qquad R(II) = \pi_R(2),$$
--
--   with the closed forms of §4.2.
--
--   Together with the manufacturers' identities they are the whole input of the contracting analysis.
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

/-- §4.2, p. 252 (with `c = c_d > 0`): in every pricing-equilibrium family the retailer's ex
ante profits are `π_R(0)`, `π_R(1)` and `π_R(2)`. -/
theorem ex_ante_profits_retailer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    let P := payoffTable μ θ Y a b c φ E
    P.R (fun _ => Status.uninformed) = piR0 a b c φ σ β ∧
    (∀ i : Fin 2, P.R (onlyInformed i) = piR1 a b c φ σ β) ∧
    P.R (fun _ => Status.informed) = piR2 a b c φ σ β := by sorry

end InfoSharing.Diseconomy
