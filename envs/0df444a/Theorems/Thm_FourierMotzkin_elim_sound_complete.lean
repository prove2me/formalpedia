-- Prove2me | Theorems.Thm_FourierMotzkin_elim_sound_complete
-- name    : FourierMotzkin.elim_sound_complete
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:43:27.408836+00:00
-- url     : https://prove2.me/theorems/23753882-b329-47ef-87cd-f8d9dc63a82a
-- title:
--   Fourier–Motzkin elimination is exact projection
-- statement:
--   Let $\mathrm{sys}$ be a finite system of linear inequalities $\sum_i a_ix_i\le b$ over the reals and $j$ a variable index. The system $\mathrm{elim}_j(\mathrm{sys})$ obtained by Fourier–Motzkin elimination of $x_j$ describes exactly the projection of the solution set along the $x_j$-axis: for every point $x$,
--   $$\exists t\in\mathbb R:\ x[x_j:=t]\ \text{satisfies}\ \mathrm{sys}\quad\Longleftrightarrow\quad x\ \text{satisfies}\ \mathrm{elim}_j(\mathrm{sys}).$$
--
--   This is the basic step of the exact linear programming solver `lpMax`.
-- source:
--   A. Schrijver, Theory of Linear and Integer Programming (1986), §12.2 (Fourier–Motzkin elimination); used for the local LPs in Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, §9.4 p.42.

import Mathlib
import Definitions.Def_FourierMotzkin_basic

namespace FourierMotzkin

/-- **Fourier–Motzkin elimination computes the projection** (Schrijver, *Theory of Linear and Integer Programming*,
§12.2). A point `x` satisfies the eliminated system `elim j sys` iff some choice of its `j`-th coordinate satisfies
`sys`. -/
theorem elim_sound_complete (j : ℕ) (sys : System) (x : ℕ → ℝ) :
    (∃ t, Sat sys (Function.update x j t)) ↔ Sat (elim j sys) x := by sorry

end FourierMotzkin
