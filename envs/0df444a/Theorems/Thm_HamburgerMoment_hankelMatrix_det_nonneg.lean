-- Prove2me | Theorems.Thm_HamburgerMoment_hankelMatrix_det_nonneg
-- name    : HamburgerMoment.hankelMatrix_det_nonneg
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:03:06.416351+00:00
-- url     : https://prove2.me/theorems/0844ad0d-ebaa-43e5-9a20-3ae1f3c881df
-- title:
--   Positivity of the Hankel kernel gives $\det\Delta_n\ge0$
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a real sequence whose Hankel kernel $A=(m_{j+k})_{j,k\ge0}$ is positive definite (the Hankel form is $\ge0$ on every finitary complex sequence). Then for every $n\ge0$ the $(n+1)\times(n+1)$ Hankel matrix
--   $$\Delta_n=\begin{pmatrix}m_0&m_1&\cdots&m_n\\ m_1&m_2&\cdots&m_{n+1}\\ \vdots&\vdots&\ddots&\vdots\\ m_n&m_{n+1}&\cdots&m_{2n}\end{pmatrix}$$
--   satisfies
--   $$\det(\Delta_n)\ \ge\ 0.$$
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Uniqueness of solutions", displayed matrix $\Delta_n$ and the sentence "Positivity of A means that, for each n, det(Δn) ≥ 0"

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem hankelMatrix_det_nonneg (m : ℕ → ℝ) (hm : HankelPosDef m) (n : ℕ) :
    0 ≤ (hankelMatrix m n).det := by sorry

end HamburgerMoment
