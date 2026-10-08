-- Prove2me | Theorems.Thm_LenstraIP_Hyperplanes_radius_lt_of_disjoint
-- name    : LenstraIP.Hyperplanes.radius_lt_of_disjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:49.635462+00:00
-- url     : https://prove2.me/theorems/40453944-87b1-4a10-996f-624e9ed2d936
-- title:
--   §1, p. 541 — if B(p, r) ⊂ τK and τK misses L, then r < ½√n|bₙ|
-- statement:
--   Let $b_1, \dots, b_n$ be a basis of $\mathbb R^n$ numbered so that $|b_n| = \max\{|b_i| : 1 \le i \le n\}$, and let $L = \sum_i \mathbb Z b_i$. Let $\tau K \subseteq \mathbb R^n$ be a set containing the closed ball $B(p, r)$ for some $p \in \mathbb R^n$ and $r > 0$, and suppose $\tau K \cap L = \emptyset$. Then
--   $$r < \tfrac12\sqrt n\,|b_n|.$$
--
--   In the paper this is the first step of the procedure: by (10) there is $y \in L$ with $|p - y| \le \tfrac12\sqrt n|b_n|$; if $y \notin \tau K$ then $y \notin B(p,r)$, so $|p-y| > r$. A lattice-point-free body therefore has inradius small compared with the longest vector of the basis.
--
--   **Formalization Note** The set $\tau K$ is an arbitrary subset $X$ of $\mathbb R^n$: the paper uses only $B(p,r) \subset \tau K$ here, not the polyhedral form of $K$ or the map $\tau$. "$\tau K \cap L = \emptyset$" is the hypothesis that no lattice point lies in $X$. $r > 0$ is the paper's convention for balls. $n = k + 1$, $b_n$ is `b (Fin.last k)`.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §1, p. 541, 'and this implies that r < ½√n |bₙ|'

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

open KannanLattice.Core

namespace LenstraIP.Hyperplanes

/-- Lenstra (1983), §1, p. 541: if `|bₙ|` is maximal, `B(p, r) ⊂ X` and `X` contains no point
of `L`, then `r < ½ √n |bₙ|`. -/
theorem radius_lt_of_disjoint (k : ℕ) (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)))
    (hb : LinearIndependent ℝ b) (hmax : ∀ i, ‖b i‖ ≤ ‖b (Fin.last k)‖)
    (X : Set (EuclideanSpace ℝ (Fin (k + 1)))) (p : EuclideanSpace ℝ (Fin (k + 1))) (r : ℝ)
    (hr : 0 < r) (hball : Metric.closedBall p r ⊆ X) (hX : ∀ y ∈ lattice b, y ∉ X) :
    r < (1 / 2 : ℝ) * Real.sqrt ((k : ℝ) + 1) * ‖b (Fin.last k)‖ := by sorry

end LenstraIP.Hyperplanes
