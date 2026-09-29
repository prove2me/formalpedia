-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage_checked_yBox_d0_contains
-- name    : GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage.checked_yBox_d0_contains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:15:14.959179+00:00
-- url     : https://prove2.me/theorems/fb933e6f-a17b-41ef-b5e7-6034eb7fd652
-- title:
--   Checked stable E8 interval graph encloses the scalar slope
-- statement:
--   Let $i$ be four dyadic intervals for a real parameter $a$, its exponential $e^{-2a}$, its logarithm $\log(1+e^{-2a})$, and $\log2$. Suppose the executable exponential and both logarithm checks accept their exact witnesses, all five denominator lower bounds are positive, and the alpha interval contains $a$. Then the zero-order component of yBox encloses the stable slope $Y(a)$. This theorem turns the finite primitive certificates into the real endpoint enclosure used by the E8 inverse-coverage proof.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellInverseCoverage.lean#L78-L93

import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core

open GeneralCK GeneralCK.Certificates
open Set GeneralCK.Certificates.DyadicInterval GeneralCK.Certificates.E8TAxisStableInterval
open GeneralCK.Certificates.E8TAxisStableScalar

theorem GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage.checked_yBox_d0_contains {p : ℕ} {i : Inputs p}
    {we : ExpWitness p} {wl wL : FastLogBoxWitness}
    (he : expBoxCheck ((ofInt p (-2)).mul i.alpha) i.expNegTwo we = true)
    (hl : logBoxCheck ((ofInt p 1).add i.expNegTwo) i.logOnePlusExp wl = true)
    (hL : logBoxCheck (ofInt p 2) i.logTwo wL = true)
    (hp : DenominatorsPositive i) {a : ℝ} (ha : i.alpha.Contains a) :
    (yBox i).d0.Contains (Y a) := by sorry
