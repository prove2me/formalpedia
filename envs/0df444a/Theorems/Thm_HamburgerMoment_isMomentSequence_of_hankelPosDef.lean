-- Prove2me | Theorems.Thm_HamburgerMoment_isMomentSequence_of_hankelPosDef
-- name    : HamburgerMoment.isMomentSequence_of_hankelPosDef
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:01:32.722304+00:00
-- url     : https://prove2.me/theorems/d2fda246-a9b6-4943-9d6b-629258264994
-- title:
--   "If": a positive definite Hankel kernel comes from a moment sequence
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a real sequence whose Hankel kernel is positive definite:
--   $$\sum_{j,k\ge0}m_{j+k}\,c_j\,\overline{c_k}\ \ge\ 0$$
--   for every finitary complex sequence $(c_j)_{j\ge0}$. Then there is a positive Borel measure $\mu$ on $\mathbb R$ such that every $x^n$ is $\mu$-integrable and
--   $$m_n=\int_{-\infty}^{\infty}x^n\,d\mu(x)\qquad(n\ge0).$$
--
--   This is the existence half of Hamburger's characterization.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Characterization", converse (sketch via the Hilbert space $\mathcal H$, the shift operator $T$ and the spectral measure of a self-adjoint extension $\overline T$); see also Chihara 1978, p. 56, Theorem 3.2

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem isMomentSequence_of_hankelPosDef (m : ℕ → ℝ) (hm : HankelPosDef m) :
    IsMomentSequence m := by sorry

end HamburgerMoment
