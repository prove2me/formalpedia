-- Prove2me | Theorems.Thm_HamburgerMoment_isMomentMeasure_convex
-- name    : HamburgerMoment.isMomentMeasure_convex
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:02:01.941001+00:00
-- url     : https://prove2.me/theorems/7004a447-1fb3-43da-9c5a-c82e249ae7be
-- title:
--   The solutions of the Hamburger moment problem form a convex set
-- statement:
--   Let $m=(m_n)_{n\ge0}$ be a real sequence and let $\mu,\nu$ be two solutions of its Hamburger moment problem (positive Borel measures on $\mathbb R$ with $x^n$ integrable and $\int x^n\,d\mu=\int x^n\,d\nu=m_n$ for all $n$). Then for every $t\in[0,1]$ the measure
--   $$t\,\mu+(1-t)\,\nu$$
--   is again a solution.
--
--   **Formalization Note** The scalars $t$ and $1-t$ act on measures through `ENNReal.ofReal`.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Uniqueness of solutions", first sentence

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem isMomentMeasure_convex (m : ℕ → ℝ) (μ ν : Measure ℝ)
    (hμ : IsMomentMeasure m μ) (hν : IsMomentMeasure m ν) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    IsMomentMeasure m (ENNReal.ofReal t • μ + ENNReal.ofReal (1 - t) • ν) := by sorry

end HamburgerMoment
