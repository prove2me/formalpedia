-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage_covers_of_endpoint_enclosures
-- name    : GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage.covers_of_endpoint_enclosures
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:19:12.476141+00:00
-- url     : https://prove2.me/theorems/a66bd44c-75d8-46f0-8a8d-f3e0816ec32c
-- title:
--   E8 inverse coverage from checked endpoint enclosures
-- statement:
--   Let $I=[L/2^p,U/2^p]$ be an ordered dyadic interval with $L>0$. Suppose two dyadic boxes enclose $Y(L/2^p)$ and $Y(U/2^p)$, and exact scaled comparisons place the first box below a requested lower slope and the second above a requested upper slope. Then every slope between those requested bounds equals $Y(a)$ for some positive $a\in I$. The stable E8 slope is continuous on the positive interval, so endpoint enclosure suffices for coverage without an injectivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellInverseCoverage.lean#L63-L76

import Mathlib.Order.Interval.Set.Defs
import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_semantic_core

open GeneralCK GeneralCK.Certificates
open Set GeneralCK.Certificates.DyadicInterval GeneralCK.Certificates.E8TAxisStableInterval
open GeneralCK.Certificates.E8TAxisStableScalar
open GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage

theorem GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage.covers_of_endpoint_enclosures {p : ℕ} {alpha loBox hiBox : DyadicInterval p}
    {sLower sUpper : ℝ}
    (hpos : 0 < alpha.lo) (horder : alpha.lo ≤ alpha.hi)
    (hl : loBox.Contains (Y (lower alpha)))
    (hu : hiBox.Contains (Y (upper alpha)))
    (hlo : (loBox.hi : ℝ) ≤ (scale p : ℝ) * sLower)
    (hhi : (scale p : ℝ) * sUpper ≤ (hiBox.lo : ℝ))
    {s : ℝ} (hs : s ∈ Icc sLower sUpper) :
    ∃ a : ℝ, alpha.Contains a ∧ 0 < a ∧ Y a = s := by sorry
