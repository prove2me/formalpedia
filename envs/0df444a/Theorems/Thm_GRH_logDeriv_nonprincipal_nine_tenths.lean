-- Prove2me | Theorems.Thm_GRH_logDeriv_nonprincipal_nine_tenths
-- name    : GRH.logDeriv_nonprincipal_nine_tenths
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:18:51.023894+00:00
-- url     : https://prove2.me/theorems/f2e76ebf-0015-4561-a496-4408ab698e60
-- title:
--   Uniform logarithmic-derivative bound for nonprincipal Dirichlet characters in the strip from nine tenths to two
-- statement:
--   There is an absolute constant $C>0$ such that, for every nonprincipal Dirichlet character $\chi$ modulo a positive integer $q$ and every $s$ with $9/10\le\operatorname{Re}s\le2$,
--   $$\left|\frac{L'}{L}(s,\chi)\right|\le C\log\!\big(q(|\operatorname{Im}s|+2)\big).$$
--
--   The bound holds at every height. It controls how much the modulus of $1/L(s,\chi)$ can change along horizontal segments inside the strip, as needed for Mellin contour arguments for the twisted Möbius sums.
-- source:
--   Independent corollary of the Davenport §16 local partial fraction expansion https://prove2.me/theorems/d5a79704-2d17-4acd-bf91-80ec20436839 and the proved uniform zero-free half-plane https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Calculus.LogDeriv

open Complex

theorem GRH.logDeriv_nonprincipal_nine_tenths :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ,
      (9 / 10 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
        C * Real.log ((q : ℝ) * (|s.im| + 2)) := by sorry
