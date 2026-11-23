-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_gauss_four_panel_upper_error
-- name    : GrothendieckLB.Supplement.gauss_four_panel_upper_error
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T20:51:10.418874+00:00
-- url     : https://prove2.me/theorems/f5ef9263-9cbf-4563-84a3-a1ed31e899d6
-- title:
--   Sharp fourth-order Gaussian quadrature rule for an eighth derivative bound
-- statement:
--   The four-node Gauss–Legendre mean on the unit interval underestimates a function’s integral by at most an upper bound on its eighth derivative divided by 1778112000. This is the sharp constant for the one-sided quadrature estimate.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix C.3–C.4; upper-bounds/theorem-cubic-quintic/certify_d3h.py.

import Definitions.Def_GrothendieckLB_Supplement_cqGaussFourPanel

namespace GrothendieckLB.Supplement

open MeasureTheory

theorem gauss_four_panel_upper_error :
    ∀ (f : ℝ → ℝ) (B : ℝ), ContDiff ℝ 8 f → (∀ x ∈ Set.Icc (0:ℝ) 1, iteratedDeriv 8 f x ≤ B) →
      (∫ x in (0:ℝ)..1, f x) ≤ CQBoundary.GaussFour.mean f + B/1778112000 := by sorry

end GrothendieckLB.Supplement
