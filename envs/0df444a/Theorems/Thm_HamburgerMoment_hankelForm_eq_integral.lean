-- Prove2me | Theorems.Thm_HamburgerMoment_hankelForm_eq_integral
-- name    : HamburgerMoment.hankelForm_eq_integral
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:57:44.680848+00:00
-- url     : https://prove2.me/theorems/4986b98c-4435-41db-8c56-466dfc23610b
-- title:
--   Hankel form as an integral: $\sum m_{j+k}c_j\overline{c_k}=\int|\sum c_jx^j|^2\,d\mu$
-- statement:
--   Let $\mu$ be a solution of the Hamburger moment problem for the real sequence $m$, i.e. a positive Borel measure on $\mathbb R$ with $x^n$ integrable and $\int x^n\,d\mu=m_n$ for all $n\ge0$. Then for every finitary complex sequence $(c_j)_{j\ge0}$,
--   $$\sum_{j,k\ge0}m_{j+k}\,c_j\,\overline{c_k}=\int_{-\infty}^{\infty}\Big|\sum_{j\ge0}c_jx^j\Big|^2\,d\mu(x).$$
--
--   This identity is the computation behind the "only if" part of Hamburger's theorem.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Characterization", displayed identity in the "only if" paragraph

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem hankelForm_eq_integral (m : ℕ → ℝ) (μ : Measure ℝ) (hμ : IsMomentMeasure m μ)
    (c : ℕ →₀ ℂ) :
    hankelForm m c =
      ((∫ x, ‖∑ j ∈ c.support, c j * (x : ℂ) ^ j‖ ^ 2 ∂μ : ℝ) : ℂ) := by sorry

end HamburgerMoment
