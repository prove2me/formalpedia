-- Prove2me | Theorems.Thm_MechanismDesign_BilateralTrade_pivot_maximizes_surplus
-- name    : MechanismDesign.BilateralTrade.pivot_maximizes_surplus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:54:26.926988+00:00
-- url     : https://prove2.me/theorems/b893780f-9a28-425f-99b0-0eb4de62bead
-- title:
--   Lemma 3.10 -- the pivot mechanism maximizes the expected surplus of payments over receipts
-- statement:
--   In the bilateral trade environment, let $q^*$ be a measurable first-best trading rule and consider the pivot mechanism built on it. Let $(q, t_S, t_B)$ be any (well-defined) incentive-compatible and individually rational direct mechanism whose trading rule $q$ is first best (with any tie rule). Then
--
--   $$
--   \mathbb E\big[t_B(\theta) - t_S(\theta)\big] \;\le\; \mathbb E\big[t_B^{\mathrm{pivot}}(\theta) - t_S^{\mathrm{pivot}}(\theta)\big].
--   $$
--
--   The ex ante expected difference between the buyer's payment and the seller's receipt is therefore largest under the pivot mechanism among all incentive-compatible and individually rational mechanisms that implement efficient trade. No budget constraint is imposed on the comparison class.
--
--   Together with Lemma 3.11 it reduces the Myerson–Satterthwaite impossibility to the sign of one number.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.67, Lemma 3.10

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Lemma 3.10 (p.67): the ex ante expected difference `E[t_B − t_S]` between the buyer's and the
seller's transfers under the pivot mechanism is at least as large as under any well-defined,
incentive-compatible and individually rational direct mechanism `m` that implements a first-best
trading rule. -/
theorem pivot_maximizes_surplus (E : Environment) (q : ℝ × ℝ → ℝ) (hq : IsFirstBestRule E q)
    (hqm : Measurable q) (m : DirectMechanism E) (hm : m.Admissible)
    (hfb : IsFirstBestRule E m.q) :
    m.expectedSurplus ≤ (pivot E q hq).expectedSurplus := by sorry

end MechanismDesign.BilateralTrade
