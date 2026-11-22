-- Prove2me | Theorems.Thm_MasulloRH_unit_height_zeta_right_rectangle_deriv_bound
-- name    : MasulloRH.unit_height_zeta_right_rectangle_deriv_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T23:41:03.982128+00:00
-- url     : https://prove2.me/theorems/724f2f12-f6c3-4346-91a0-da366324b4c2
-- title:
--   An explicit rational derivative bound on every right-hand unit-band rectangle
-- statement:
--   For natural numbers $n,k$, put $d=1/(k+3)$ and
--
--   $$R_{n,k}=[1/2+d,1]\times[100000+n+d,100001+n]\subset\mathbb C.$$
--
--   Every $s\in R_{n,k}$ satisfies
--
--   $$|\zeta'(s)|\le16(100003+n).$$
--
--   The upper bound is an explicit nonnegative integer, hence a rational witness for the derivative part of the open rectangle mesh certificate. It is uniform in $k$. The rectangle has height $1-d$ inside a unit band. No lower bound on $|\zeta|$ or assertion of nonvanishing is included.
-- source:
--   Original explicit certificate-support estimate for https://prove2.me/theorems/f9f6d44b-a148-4b98-8aa0-a911a4eaa8b4 . Uses the proved classical Euler–Maclaurin bound Zeta23.RvM.norm_riemannZeta_le_of_re_pos, https://prove2.me/theorems/f49f0c25-9fc8-49f9-b17c-64f059e1981d , and the Cauchy derivative estimate in Mathlib.Analysis.Complex.Liouville (Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474). No dependence on the Alpöge RH proof; no claim that the rectangle nonvanishing frontier is closed.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false

theorem MasulloRH.unit_height_zeta_right_rectangle_deriv_bound (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
      ‖deriv riemannZeta s‖ ≤ (16 : ℝ) * (100003 + n) := by sorry
