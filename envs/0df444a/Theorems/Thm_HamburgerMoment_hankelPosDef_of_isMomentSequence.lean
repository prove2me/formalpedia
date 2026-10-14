-- Prove2me | Theorems.Thm_HamburgerMoment_hankelPosDef_of_isMomentSequence
-- name    : HamburgerMoment.hankelPosDef_of_isMomentSequence
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:01:06.610085+00:00
-- url     : https://prove2.me/theorems/9799d852-c0d4-4ae3-9865-94f17b91fac5
-- title:
--   "Only if": a moment sequence has a positive definite Hankel kernel
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a real sequence that is the moment sequence of some positive Borel measure on $\mathbb R$. Then its Hankel kernel is positive definite:
--   $$\sum_{j,k\ge0}m_{j+k}\,c_j\,\overline{c_k}\ \ge\ 0$$
--   for every finitary complex sequence $(c_j)_{j\ge0}$.
--
--   This is the necessity half of Hamburger's characterization.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Characterization", "only if" paragraph

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem hankelPosDef_of_isMomentSequence (m : ℕ → ℝ) (hm : IsMomentSequence m) :
    HankelPosDef m := by sorry

end HamburgerMoment
