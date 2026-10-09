-- Prove2me | Theorems.Thm_LatticeHamSim_CommLR_eq_28
-- name    : LatticeHamSim.CommLR.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:53.052284+00:00
-- url     : https://prove2.me/theorems/889c1973-4034-4ee7-8d87-04cfc1c926e7
-- title:
--   (28), p. 23 — four initial and uniform bounds for C_B and D_B
-- statement:
--   Let $h_X$ be Hermitian operators supported on $X$, let $H=\sum_Xh_X$, and let $B$ be supported on $Y$. For any set $Z$ and time $t$, write $\delta_{Z\sim Y}=1$ when $Z$ meets $Y$ and $0$ otherwise. Equation (28) gives all four bounds
--
--   $$C_B(Z,0)\le2\|B\|\delta_{Z\sim Y},\quad C_B(Z,t)\le2\|B\|,\quad D_B(Z,0)\le2\|B\|\|h_Z\|\delta_{Z\sim Y},\quad D_B(Z,t)\le2\|B\|\|h_Z\|.$$
--
--   The time-zero factors record locality: operators on disjoint supports commute. The uniform bounds provide initial estimates for the integral and series inequalities.
--
--   **Formalization Note** $\|\cdot\|$ is the L2 operator norm on finite complex matrices. No assumption (14) or (15) is needed here.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 23, Appendix C.2, (28), indicator convention p. 24

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

/-- The four bounds in (28), including the overlap indicators at time zero. -/
theorem eq_28 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (Y : Finset Λ) (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hB : SupportedOn Y B) (Z : Finset Λ) (t : ℝ) :
    CB h B Z 0 ≤ 2 * ‖B‖ * indicator (meets Z Y) ∧
    CB h B Z t ≤ 2 * ‖B‖ ∧
    DB h B Z 0 ≤ 2 * ‖B‖ * ‖h Z‖ * indicator (meets Z Y) ∧
    DB h B Z t ≤ 2 * ‖B‖ * ‖h Z‖ := by sorry

end LatticeHamSim.CommLR
