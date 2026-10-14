-- Prove2me | Theorems.Thm_HamburgerMoment_unique_of_abs_le_factorial
-- name    : HamburgerMoment.unique_of_abs_le_factorial
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:04:23.219508+00:00
-- url     : https://prove2.me/theorems/8aa3486d-502d-4cfe-a31d-fe2045be08fa
-- title:
--   Uniqueness under the growth bound $|m_n|\le CD^nn!$
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a real sequence and suppose there are constants $C,D$ such that
--   $$|m_n|\ \le\ C\,D^n\,n!\qquad\text{for all }n\ge0.$$
--   Then the Hamburger moment problem for $m$ has at most one solution: if $\mu$ and $\nu$ are positive Borel measures on $\mathbb R$ with $x^n$ integrable and $\int x^n\,d\mu=\int x^n\,d\nu=m_n$ for all $n$, then $\mu=\nu$.
--
--   This growth condition is a special case of Carleman's condition.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Uniqueness of solutions", sentence "More generally, the solution is unique if there are constants C and D such that, for all n, |mn| ≤ CD^n n! (Reed & Simon 1975, p. 205)"

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem unique_of_abs_le_factorial (m : ℕ → ℝ) (C D : ℝ)
    (hCD : ∀ n : ℕ, |m n| ≤ C * D ^ n * (n.factorial : ℝ))
    (μ ν : Measure ℝ) (hμ : IsMomentMeasure m μ) (hν : IsMomentMeasure m ν) :
    μ = ν := by sorry

end HamburgerMoment
