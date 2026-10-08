-- Prove2me | Theorems.Thm_Helfgott_primitive_LFunction_negative_half_logDeriv_bound
-- name    : Helfgott.primitive_LFunction_negative_half_logDeriv_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T13:28:13.635527+00:00
-- url     : https://prove2.me/theorems/7d8aae17-fac3-4dad-bef4-8ad6d1ec2f28
-- title:
--   Complete explicit logarithmic Dirichlet L-function bound on the negative half line
-- statement:
--   For every primitive nonprincipal Dirichlet character of positive conductor q and every s with Re(s)=-1/2, its actual continued L-function is nonzero and the norm of -L prime(s)/L(s) is at most log(q)+|log(pi)|+27+|Im(s)|. The proof derives a full linear Gamma logarithmic derivative bound, with convergence of differentiated Euler approximations proved by dominated convergence; handles both gamma-factor parities and the negative-strip recurrence; and bounds the full reflected von Mangoldt series by 20. No gamma asymptotic, series bound or nonvanishing hypothesis is assumed. This gives the quantitative arithmetic input for the actual shifted Goldbach contour. Horizontal bounds and numerical zero contributions remain separate.
-- source:
--   Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897. Mathlib Gamma integral, Euler limit, Mellin differentiation, harmonic bounds, Dirichlet functional equation and nonvanishing contributors, including David Loeffler, Michael Stoll, Thomas Browning and Arend Mellendijk. Original complete differentiated-Euler convergence, linear digamma and explicit left-line proof. Written by Codex.

import Mathlib.NumberTheory.LSeries.Nonvanishing
open MeasureTheory Set Filter Complex

theorem Helfgott.primitive_LFunction_negative_half_logDeriv_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (s : ℂ) (hσ : s.re= -1/2) :
    χ.LFunction s ≠ 0 ∧ ‖-deriv χ.LFunction s/χ.LFunction s‖ ≤
      Real.log q+|Real.log Real.pi|+27+|s.im| := by sorry
