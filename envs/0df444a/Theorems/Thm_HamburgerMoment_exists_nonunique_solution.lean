-- Prove2me | Theorems.Thm_HamburgerMoment_exists_nonunique_solution
-- name    : HamburgerMoment.exists_nonunique_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:04:57.341151+00:00
-- url     : https://prove2.me/theorems/7b344331-e964-448c-9b9a-59e31d4f8cf6
-- title:
--   Some moment sequences have more than one solution
-- statement:
--   There exist a real sequence $m=(m_n)_{n\ge0}$ and two different positive Borel measures $\mu\ne\nu$ on $\mathbb R$ that both solve its Hamburger moment problem:
--   $$\int_{-\infty}^{\infty}x^n\,d\mu(x)=\int_{-\infty}^{\infty}x^n\,d\nu(x)=m_n\qquad(n\ge0),$$
--   with all these integrals finite.
--
--   So the moment sequence does not determine the measure in general; a classical example is the log-normal distribution.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Uniqueness of solutions", sentence "There are examples where the solution is not unique" (Chihara 1978, p. 73)

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem exists_nonunique_solution :
    ∃ (m : ℕ → ℝ) (μ ν : Measure ℝ), IsMomentMeasure m μ ∧ IsMomentMeasure m ν ∧ μ ≠ ν := by sorry

end HamburgerMoment
