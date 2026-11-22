-- Prove2me | Theorems.Thm_NoHair_reissnerNordstrom_lapse_of_radial_equation
-- name    : NoHair.reissnerNordstrom_lapse_of_radial_equation
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:51:19.49395+00:00
-- url     : https://prove2.me/theorems/190084f5-72d3-47ab-b5a2-12080417190d
-- title:
--   Recovering the Reissner–Nordström lapse and outer horizon from the radial equation
-- statement:
--   Let $R>0$, let $e$ be real, and let the squared lapse $A$ be continuous on $[R,\infty)$, zero at $R$, and positive at every larger radius. Suppose the spherical mass equation holds for $r>R$,
--
--   $$
--   \frac{d}{dr}\bigl[r(1-A(r))\bigr]=\frac{e^2}{r^2}.
--   $$
--
--   There exists a positive mass $m$ with
--
--   $$
--   e^2\le m^2,\qquad R=m+\sqrt{m^2-e^2},\qquad
--   r^2(1-A(r))=2mr-e^2\quad(r>R).
--   $$
--
--   The boundary and positivity conditions select the outer horizon, including a double root in the extremal case.
-- source:
--   H. S. Reall, Part III Black Holes (2024), §6.1, p. 82, equations (6.2)–(6.6), https://www.damtp.cam.ac.uk/user/hsr1000/black_holes_lectures_2024.pdf. One-variable reconstruction of equations (6.4)–(6.5) from the radial mass equation and the horizon boundary condition.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Set

theorem NoHair.reissnerNordstrom_lapse_of_radial_equation (R e : ℝ) (A : ℝ → ℝ)
    (hR : 0 < R) (hA : ContinuousOn A (Ici R)) (horizon : A R = 0)
    (hpos : ∀ r, R < r → 0 < A r)
    (hrad : ∀ r, R < r → HasDerivAt (fun s => s * (1 - A s)) (e ^ 2 / r ^ 2) r) :
    ∃ m : ℝ, 0 < m ∧ e ^ 2 ≤ m ^ 2 ∧ R = m + Real.sqrt (m ^ 2 - e ^ 2) ∧
      ∀ r, R < r → r ^ 2 * (1 - A r) = 2 * m * r - e ^ 2 := by
  sorry
