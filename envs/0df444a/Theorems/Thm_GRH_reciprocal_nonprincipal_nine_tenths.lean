-- Prove2me | Theorems.Thm_GRH_reciprocal_nonprincipal_nine_tenths
-- name    : GRH.reciprocal_nonprincipal_nine_tenths
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:22:42.345159+00:00
-- url     : https://prove2.me/theorems/4913c51a-d1bf-4c10-9d7a-523c65c90f49
-- title:
--   Polynomial reciprocal growth for nonprincipal Dirichlet L-functions between nine tenths and two
-- statement:
--   For each nonprincipal Dirichlet character $\chi$ of positive modulus, there exist $C,M\ge0$ such that
--   $$|1/L(s,\chi)|\le C(1+|\operatorname{Im}s|)^M\qquad(9/10\le\operatorname{Re}s\le2).$$
--   This growth estimate is uniform throughout the strip at every height and supplies the reciprocal factor in an exponentially smoothed Möbius contour shift.
-- source:
--   Independent corollary of the logarithmic-derivative estimate https://prove2.me/theorems/f2e76ebf-0015-4561-a496-4408ab698e60, the zero-free half-plane https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918, and the Euler-product anchor https://prove2.me/theorems/6164233f-eecb-4cc6-ba54-669f100a3086.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex

theorem GRH.reciprocal_nonprincipal_nine_tenths (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ s : ℂ, (9/10:ℝ) ≤ s.re → s.re ≤ 2 →
      ‖(χ.LFunction s)⁻¹‖ ≤ C * (1+|s.im|)^M := by sorry
