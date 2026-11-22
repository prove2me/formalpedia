-- Prove2me | Theorems.Thm_MasulloRH_euler_train_signed_spectrum_and_order_gap
-- name    : MasulloRH.euler_train_signed_spectrum_and_order_gap
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T23:55:56.376261+00:00
-- url     : https://prove2.me/theorems/56fd91db-2d52-49c7-b8f6-b738729edfda
-- title:
--   Spectrum witnesses and sharp distance from semidefinite operators for the full Euler cell train
-- statement:
--   For $0<r<1$ and any unit complex phase $u$, let $e$ be the first coordinate vector of $\ell^2(\mathbb N;\mathbb C)$ and let $c=\sqrt{1-r^2}$. The full geometric sequence $t_n=c(r\overline u)^n$ is a unit vector. Write $D=P_t-P_e$ for the difference of its orthogonal line projection and the zeroth-cell line projection. The vectors $ct+(r-1)e$ and $ct+(-r-1)e$ are nonzero eigenvectors of $D$ with eigenvalues $r$ and $-r$. One has $\lVert D\rVert=r$. For every bounded positive operator $B$, both $\lVert D-B\rVert$ and $\lVert D+B\rVert$ are at least $r$. Zero attains each lower bound.
-- source:
--   Auxiliary to the Masullo mission, frozen November 20, 2026 manuscript §§7.3.2 and 11.3.2. Yi’s cell-block calculation, theorem b07affbd-42a1-483c-b695-0127ef211b1c, gives the geometric Gram coefficients and winding reconstruction. The cumulative comparison is in mission comment e0838ea1-7f9f-458a-a461-b6aa255f7018. This theorem treats the spectrum and order distance of the infinite scalar cell factor. Connecting that factor with adelic range projections uses the separate analytic comparison.

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open InnerProductSpace
open scoped ComplexConjugate

theorem MasulloRH.euler_train_signed_spectrum_and_order_gap (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (u : ℂ) (hu : ‖u‖ = 1) :
    let H := lp (fun _ : ℕ => ℂ) 2
    let e : H := lp.single 2 0 1
    let c : ℂ := Real.sqrt (1-r^2)
    ∃ t : H, (∀ n : ℕ, t n = c * ((r : ℂ) * conj u)^n) ∧ ‖t‖ = 1 ∧
      let D := rankOne ℂ t t - rankOne ℂ e e
      let xp := c • t + ((r : ℂ) - 1) • e
      let xm := c • t + (-(r : ℂ) - 1) • e
      xp ≠ 0 ∧ xm ≠ 0 ∧ D xp = (r : ℂ) • xp ∧ D xm = -(r : ℂ) • xm ∧
        ‖D‖ = r ∧ ∀ B : H →L[ℂ] H, B.IsPositive → r ≤ ‖D - B‖ ∧ r ≤ ‖D + B‖ := by sorry
