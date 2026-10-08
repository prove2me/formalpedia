-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_lowest_type_binding
-- name    : MechanismDesign.Auctions.lowest_type_binding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:45:09.320232+00:00
-- url     : https://prove2.me/theorems/92113288-8221-4eab-a2e7-e07b1e3caec6
-- title:
--   Lemma 3.5 -- a revenue-maximizing mechanism leaves the lowest type zero utility
-- statement:
--   Consider the class of well-defined, incentive-compatible and individually rational direct mechanisms in the single-unit auction environment.
--
--   **Lemma 3.5.** If a mechanism in this class maximizes the seller's expected revenue $\mathbb E\big[\sum_i t_i(\theta)\big]$ over the class, then for every buyer $i$
--   $$T_i(\underline\theta) = \underline\theta\, Q_i(\underline\theta).$$
--
--   Combined with Proposition 3.2 this determines all interim payments of an optimal mechanism from its allocation rule (Eq. (3.3)).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.39, Lemma 3.5

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.5, p.39: if an incentive-compatible, individually rational direct mechanism
maximizes the seller's expected revenue among all such mechanisms, then
`T_i(θ̲) = θ̲ Q_i(θ̲)` for every buyer `i`. -/
theorem lowest_type_binding {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hm : m.Admissible)
    (hopt : ∀ m' : DirectMechanism E, m'.Admissible → m'.revenue ≤ m.revenue) :
    ∀ i, m.interimT i E.lo = E.lo * m.interimQ i E.lo := by sorry

end MechanismDesign.Auctions
