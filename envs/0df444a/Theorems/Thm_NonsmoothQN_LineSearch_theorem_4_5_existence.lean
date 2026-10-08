-- Prove2me | Theorems.Thm_NonsmoothQN_LineSearch_theorem_4_5_existence
-- name    : NonsmoothQN.LineSearch.theorem_4_5_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:02.514358+00:00
-- url     : https://prove2.me/theorems/77461bdb-8814-4966-9b16-e5fa950f4c9b
-- title:
--   Theorem 4.5, p. 146 — under Assumption 4.1 the Armijo–Wolfe steps have nonzero measure
-- statement:
--   Let $h$ satisfy Assumption 4.1 with slope $s=\limsup_{t\downarrow0}h(t)/t<0$, and let $0<c_1<c_2<1$. Then the set of Armijo–Wolfe steps,
--   $$\{t>0 : h(t)<c_1st,\ h \text{ is differentiable at } t,\ h'(t)>c_2s\},$$
--   has nonzero Lebesgue measure.
--
--   In particular an Armijo–Wolfe step exists, and a line search that samples steps cannot be defeated by the nondifferentiable points of $h$, which form a null set.
--
--   **Formalization Note.** "Nonzero measure" is `volume S ≠ 0` in $[0,\infty]$.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 146, Theorem 4.5

import Mathlib
import Definitions.Def_NonsmoothQN_LineSearch_Basic

open Filter Topology MeasureTheory Set

namespace NonsmoothQN.LineSearch

/-- Theorem 4.5 (existence of step, p. 146). Under Assumption 4.1, with `0 < c₁ < c₂ < 1`, the
set of Armijo–Wolfe steps has nonzero measure. -/
theorem theorem_4_5_existence (h : ℝ → ℝ) (c₁ c₂ s : ℝ)
    (hA41 : Assumption41 h s) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    volume {t | IsAWStep h c₁ c₂ s t} ≠ 0 := by sorry

end NonsmoothQN.LineSearch
