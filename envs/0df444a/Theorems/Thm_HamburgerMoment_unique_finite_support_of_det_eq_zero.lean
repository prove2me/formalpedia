-- Prove2me | Theorems.Thm_HamburgerMoment_unique_finite_support_of_det_eq_zero
-- name    : HamburgerMoment.unique_finite_support_of_det_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:03:52.579919+00:00
-- url     : https://prove2.me/theorems/8495483b-8bbd-4c6c-9015-e714681c80a8
-- title:
--   If $\det\Delta_n=0$ for some $n$, the solution is unique and finitely supported
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a real sequence whose Hankel kernel is positive definite, and suppose that
--   $$\det(\Delta_n)=0$$
--   for some $n\ge0$, where $\Delta_n=(m_{i+j})_{0\le i,j\le n}$. Then the Hamburger moment problem for $m$ has exactly one solution $\mu$, and $\mu$ has finite support: there is a finite set $S\subset\mathbb R$ with $\mu(\mathbb R\setminus S)=0$.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Uniqueness of solutions", sentence "If det(Δn) = 0, for some n, then (H, ⟨,⟩) is finite-dimensional and T is self-adjoint. So in this case the solution to the Hamburger moment problem is unique and μ ... has finite support"

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem unique_finite_support_of_det_eq_zero (m : ℕ → ℝ) (hm : HankelPosDef m) (n : ℕ)
    (hdet : (hankelMatrix m n).det = 0) :
    ∃ μ : Measure ℝ, (∀ ν : Measure ℝ, IsMomentMeasure m ν ↔ ν = μ) ∧
      ∃ S : Finset ℝ, μ (↑S)ᶜ = 0 := by sorry

end HamburgerMoment
