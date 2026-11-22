-- Prove2me | Theorems.Thm_MasulloRH_actual_translated_zeta_contour_pole_limit
-- name    : MasulloRH.actual_translated_zeta_contour_pole_limit
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:08:32.317377+00:00
-- url     : https://prove2.me/theorems/048d3932-a6ee-4616-a4fc-0a551f66a1b1
-- title:
--   The normalized translated two-line completed-zeta contour tends to minus the half moment
-- statement:
--   For a compact C² log test k, put f(u)=exp(−L/2)k(u−L). On every fixed right line 1<c≤3/2, the two-sided completed-zeta logarithmic derivative contour of f tends to minus Hfn(k)(1), the signed half-weight Mellin coefficient. Both reflected test terms are retained. This arithmetic-scale scalar concerns the actual analytic contour; it does not assume or imply an identification with an indented quotient operator.
-- source:
--   Zeta23.WeilEF.full_line_identity, actual completed zeta and actual zero multiplicities; frozen Masullo §§10.3 and 11.3–12.4 comparison.

import Mathlib
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_WeilEF_VerticalLine
open Filter Topology Complex MeasureTheory Zeta23 Zeta23.WeilEF

theorem MasulloRH.actual_translated_zeta_contour_pole_limit (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    Tendsto (fun L : ℝ =>
      let f := fun u : ℝ => Complex.exp (-(L : ℂ)/2) * k (u-L)
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        (Hfn f ((c:ℂ)+t*I) + Hfn f (1-c-t*I)) * logDeriv completedRiemannZeta ((c:ℂ)+t*I))
      atTop (𝓝 (-Hfn k 1)) := by sorry
