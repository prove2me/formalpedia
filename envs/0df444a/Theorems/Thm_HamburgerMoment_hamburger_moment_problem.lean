-- Prove2me | Theorems.Thm_HamburgerMoment_hamburger_moment_problem
-- name    : HamburgerMoment.hamburger_moment_problem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:56:20.642178+00:00
-- url     : https://prove2.me/theorems/f0b210eb-b01c-4a47-a288-e0c4211f3fbf
-- title:
--   Hamburger's theorem: $m$ is a moment sequence iff its Hankel kernel is positive definite
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a sequence of real numbers. The Hamburger moment problem for $m$ is solvable — that is, there is a positive Borel measure $\mu$ on $\mathbb R$ with all moments finite and
--   $$m_n=\int_{-\infty}^{\infty}x^n\,d\mu(x)\qquad(n\ge0)$$
--   — if and only if the Hankel kernel $A=(m_{j+k})_{j,k\ge0}$ is positive definite, i.e.
--   $$\sum_{j,k\ge0}m_{j+k}\,c_j\,\overline{c_k}\ \ge\ 0$$
--   for every finitary sequence $(c_j)_{j\ge0}$ of complex numbers ($c_j=0$ for all but finitely many $j$).
--
--   This is the main theorem of the mission: it reduces the existence of a representing measure to positivity conditions on the data.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Characterization", first paragraph and displayed condition

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem hamburger_moment_problem (m : ℕ → ℝ) :
    IsMomentSequence m ↔ HankelPosDef m := by sorry

end HamburgerMoment
