-- Prove2me | Theorems.Thm_HamburgerMoment_isMomentSequence_iff_hankelMatrix_posSemidef
-- name    : HamburgerMoment.isMomentSequence_iff_hankelMatrix_posSemidef
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:06:24.778132+00:00
-- url     : https://prove2.me/theorems/5aba77bc-675d-4255-a7db-f5ae24b4d169
-- title:
--   $m$ is a moment sequence iff every real Hankel matrix $\Delta_n$ is positive semidefinite
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a real sequence. Then $m$ is the moment sequence of some positive Borel measure on $\mathbb R$ if and only if, for every $n\ge0$, the real Hankel matrix
--   $$\Delta_n=(m_{i+j})_{0\le i,j\le n}$$
--   is positive semidefinite.
--
--   This is the real-coefficient form of Hamburger's characterization: positive semidefiniteness of the Hankel matrices is necessary for $m$ to be a moment sequence and sufficient for the existence of a positive measure.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef` (symmetric, with $x^{\mathsf T}\Delta_nx\ge0$ for all $x\in\mathbb R^{n+1}$).
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Polynomials", sentence "This is a necessary condition for a sequence to be a moment sequence and a sufficient condition for the existence of a positive measure" (Schmüdgen 2017, p. 2)

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem isMomentSequence_iff_hankelMatrix_posSemidef (m : ℕ → ℝ) :
    IsMomentSequence m ↔ ∀ n : ℕ, (hankelMatrix m n).PosSemidef := by sorry

end HamburgerMoment
