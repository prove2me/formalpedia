-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_sub_mem_basisCone
-- name    : Gomory69.Asymptotic.sub_mem_basisCone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:03:24.967445+00:00
-- url     : https://prove2.me/theorems/07115c1f-8152-4828-857a-ae19da363132
-- title:
--   Proof of THEOREM 4, p. 462 — y ∈ K_B(d) and ‖v‖ ≤ d imply y − v ∈ K_B
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, $K_B=\{y\in\mathbb R^m:B^{-1}y\ge0\}$, and $K_B(d)$ the set of points of $K_B$ at Euclidean distance at least $d$ from the frontier of $K_B$. If $y\in K_B(d)$ and $v\in\mathbb R^m$ has Euclidean length $\|v\|\le d$, then
--
--   $$y-v\in K_B.$$
--
--   In the proof of THEOREM 4 this is applied with $y=b$, $v=Nx_N^*$ and $d=l_{\max}(D-1)$, giving $B^{-1}(b-Nx_N^*)\ge0$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 462, proof of THEOREM 4

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- Proof of THEOREM 4 (p. 462): if `y ∈ K_B(d)` and `v` has Euclidean length at most `d`,
then `y − v ∈ K_B`. -/
theorem sub_mem_basisCone {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0)
    (d : ℝ) (y v : Fin m → ℝ) (hy : y ∈ deepCone B d) (hv : euclNorm v ≤ d) :
    y - v ∈ basisCone B := by sorry

end Gomory69.Asymptotic
