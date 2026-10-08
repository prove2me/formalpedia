-- Prove2me | Theorems.Thm_MechanismDesign_BilateralTrade_pivot_deficit
-- name    : MechanismDesign.BilateralTrade.pivot_deficit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:54:50.298881+00:00
-- url     : https://prove2.me/theorems/806657d7-1d89-4828-9bc9-b9d5dd4930ad
-- title:
--   Lemma 3.11 -- the pivot mechanism runs an expected deficit in every nontrivial case
-- statement:
--   In the bilateral trade environment, suppose $\underline\theta_B < \overline\theta_S$ and $\overline\theta_B > \underline\theta_S$, so that the condition of Proposition 3.12 fails. Let $q^*$ be a measurable first-best trading rule. Then under the pivot mechanism built on $q^*$,
--
--   $$
--   \mathbb E\big[t_B(\theta) - t_S(\theta)\big] < 0 .
--   $$
--
--   Combined with Lemma 3.10, no incentive-compatible, individually rational mechanism implementing efficient trade can balance its budget in these cases.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.68, Lemma 3.11

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Lemma 3.11 (p.68): if `θ̲_B < θ̄_S` and `θ̄_B > θ̲_S`, the ex ante expected difference
`E[t_B − t_S]` between the buyer's and the seller's transfers under the pivot mechanism is
negative. -/
theorem pivot_deficit (E : Environment) (q : ℝ × ℝ → ℝ) (hq : IsFirstBestRule E q)
    (hqm : Measurable q) (hB : E.loB < E.hiS) (hS : E.loS < E.hiB) :
    (pivot E q hq).expectedSurplus < 0 := by sorry

end MechanismDesign.BilateralTrade
