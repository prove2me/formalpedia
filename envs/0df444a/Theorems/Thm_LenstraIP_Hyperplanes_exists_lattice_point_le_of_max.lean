-- Prove2me | Theorems.Thm_LenstraIP_Hyperplanes_exists_lattice_point_le_of_max
-- name    : LenstraIP.Hyperplanes.exists_lattice_point_le_of_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:21.825975+00:00
-- url     : https://prove2.me/theorems/9f93a5ed-3d8b-4cdf-b5f3-56e7bac2f224
-- title:
--   §1, p. 540, (10) — if |bₙ| is maximal, every x ∈ ℝⁿ has a lattice point y with |x − y| ≤ ½√n|bₙ|
-- statement:
--   Let $b_1, \dots, b_n$ be a basis of $\mathbb R^n$, $L = \sum_i \mathbb Z b_i$, and suppose the basis is numbered so that $b_n$ is a longest vector:
--   $$|b_n| = \max\{ |b_i| : 1 \le i \le n \}.$$
--   Then
--   $$\forall x \in \mathbb R^n\ \exists y \in L:\quad |x - y| \le \tfrac12 \sqrt n\, |b_n|.$$
--
--   This is equation (10) of §1, the form of the LEMMA (8) that the algorithm uses: applied to the centre $p$ of an inscribed ball, it shows that a lattice-point-free body cannot contain a ball of radius $\tfrac12\sqrt n|b_n|$. For $L = \mathbb Z^n$ it is the published `QFS.exists_lattice_mem_closedBall`; the stronger Gram–Schmidt form is `KannanLattice.Core.exists_lattice_point_near_projection`.
--
--   **Formalization Note** $n = k + 1$ and $b_n$ is `b (Fin.last k)`; the maximality is the hypothesis $|b_i| \le |b_n|$ for every $i$. "Basis" is linear independence of the $n$ vectors over $\mathbb R$; $\sqrt n$ is `Real.sqrt (k + 1)`.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §1, p. 540, (10)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

open KannanLattice.Core

namespace LenstraIP.Hyperplanes

/-- Lenstra (1983), §1, p. 540, (10): if the basis is numbered so that `|bₙ|` is maximal
(here `n = k + 1` and `bₙ = b (Fin.last k)`), every `x ∈ ℝⁿ` has a lattice point `y` with
`|x − y| ≤ ½ √n |bₙ|`. -/
theorem exists_lattice_point_le_of_max (k : ℕ) (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)))
    (hb : LinearIndependent ℝ b) (hmax : ∀ i, ‖b i‖ ≤ ‖b (Fin.last k)‖)
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    ∃ y ∈ lattice b,
      ‖x - y‖ ≤ (1 / 2 : ℝ) * Real.sqrt ((k : ℝ) + 1) * ‖b (Fin.last k)‖ := by sorry

end LenstraIP.Hyperplanes
