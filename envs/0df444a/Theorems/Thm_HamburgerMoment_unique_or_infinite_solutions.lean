-- Prove2me | Theorems.Thm_HamburgerMoment_unique_or_infinite_solutions
-- name    : HamburgerMoment.unique_or_infinite_solutions
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:02:45.357226+00:00
-- url     : https://prove2.me/theorems/194322c8-5297-4829-9d32-37b9a9831ccf
-- title:
--   A solvable Hamburger moment problem has a unique solution or infinitely many
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a moment sequence, i.e. its Hamburger moment problem has at least one solution. Then at least one of the following holds:
--
--   1. the problem has a unique solution $\mu$;
--   2. the set of solutions $\{\mu : \mu \text{ positive Borel measure on }\mathbb R,\ \int x^n\,d\mu=m_n\ \forall n\}$ is infinite.
--
--   **Formalization Note** The statement is the disjunction "unique solution or infinitely many solutions"; the two alternatives are automatically exclusive.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Uniqueness of solutions", first sentence

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem unique_or_infinite_solutions (m : ℕ → ℝ) (hm : IsMomentSequence m) :
    (∃! μ : Measure ℝ, IsMomentMeasure m μ) ∨ {μ : Measure ℝ | IsMomentMeasure m μ}.Infinite := by sorry

end HamburgerMoment
