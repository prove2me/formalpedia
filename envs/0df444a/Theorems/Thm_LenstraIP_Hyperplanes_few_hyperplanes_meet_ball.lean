-- Prove2me | Theorems.Thm_LenstraIP_Hyperplanes_few_hyperplanes_meet_ball
-- name    : LenstraIP.Hyperplanes.few_hyperplanes_meet_ball
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:39.275832+00:00
-- url     : https://prove2.me/theorems/ecfc67df-e92f-4162-8f54-1e202b5259d5
-- title:
--   §1, p. 541 — if τK misses the lattice, fewer than 1 + c₁c₂√n hyperplanes H + kbₙ meet B(p, R)
-- statement:
--   Let $b_1, \dots, b_n$ be a basis of $\mathbb R^n$ ($n \ge 1$) and $L = \sum_i \mathbb Z b_i$ with determinant $d(L) = |\det(b_1,\dots,b_n)|$. Following the procedure of §1, assume that
--
--   1. the basis is **reduced** in the sense of (7): $\prod_{i=1}^n |b_i| \le c_2\cdot d(L)$, and it is "numbered such that $|b_n| = \max\{|b_i| : 1 \le i \le n\}$";
--   2. a set $\tau K \subseteq \mathbb R^n$ is sandwiched between two concentric closed balls, (3): $B(p, r) \subset \tau K \subset B(p, R)$, with $r > 0$;
--   3. the radii satisfy (4): $R / r \le c_1$.
--
--   Let $H = \sum_{i=1}^{n-1}\mathbb R b_i$. Then **either** $\tau K \cap L \neq \emptyset$, **or** only finitely many of the parallel hyperplanes $H + kb_n$ ($k \in \mathbb Z$) meet $B(p, R)$, and their number $t$ satisfies
--   $$t - 1 < c_1 c_2 \sqrt n .$$
--
--   This is the geometric core of Lenstra's algorithm (§1, p. 541): "so $t - 1 < c_1c_2\sqrt n$. Hence the number of values for $k$ that have to be considered is bounded by a constant only depending on $n$." Every lattice point of $\tau K$ lies on one of the $t$ hyperplanes, so a lattice-point search in dimension $n$ splits into fewer than $1 + c_1c_2\sqrt n$ searches in dimension $n-1$.
--
--   **Formalization Note** $\tau K$ is an arbitrary subset $X$ of $\mathbb R^n$: §1's argument uses only (3), not that $K$ is a polyhedron $\{x : Ax \le b\}$ nor the map $\tau$, and every lattice $L = \tau\mathbb Z^n$ is $\sum_i \mathbb Z b_i$ with $b_i = \tau(e_i)$ (p. 540). The paper's "for some $p \in \tau K$" follows from $B(p,r)\subset\tau K$ and $r > 0$. The constants $c_1, c_2$ ("only depending on $n$") are arbitrary real numbers; the dichotomy is about the whole lattice, not the single lattice point the procedure computes. The hyperplane count is the cardinality of the set of $k \in \mathbb Z$ with $(H + kb_n)\cap B(p,R) \ne \emptyset$ (called `hitIndices`, index `j` in Lean), finiteness being part of the conclusion. $n = k + 1$, $b_n$ is `b (Fin.last k)`, $\sqrt n$ is `Real.sqrt (k + 1)`.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §1, p. 541, 'so t − 1 < c₁c₂√n'; hypotheses (3), (4) p. 539, (7) p. 540, maximality of |bₙ| p. 541

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

open KannanLattice.Core

namespace LenstraIP.Hyperplanes

/-- Lenstra (1983), §1, p. 541: let `b₁, …, bₙ` (`n = k + 1`) be a basis of `L` with
`∏ |bᵢ| ≤ c₂ · d(L)` (7) and `|bₙ|` maximal, and let `B(p, r) ⊂ X ⊂ B(p, R)` (3) with
`R/r ≤ c₁` (4) (`X` plays the role of `τK`). Then either `X` contains a point of `L`, or only
finitely many hyperplanes `H + j·bₙ` meet `B(p, R)`, and their number `t` satisfies
`t − 1 < c₁ c₂ √n`. -/
theorem few_hyperplanes_meet_ball (k : ℕ) (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)))
    (hb : LinearIndependent ℝ b) (c₁ c₂ : ℝ) (h7 : ∏ i, ‖b i‖ ≤ c₂ * latDet b)
    (hmax : ∀ i, ‖b i‖ ≤ ‖b (Fin.last k)‖)
    (X : Set (EuclideanSpace ℝ (Fin (k + 1)))) (p : EuclideanSpace ℝ (Fin (k + 1))) (r R : ℝ)
    (hr : 0 < r) (h3l : Metric.closedBall p r ⊆ X) (h3r : X ⊆ Metric.closedBall p R)
    (h4 : R / r ≤ c₁) :
    (∃ y ∈ lattice b, y ∈ X) ∨
      ((hitIndices b p R).Finite ∧
        ((hitIndices b p R).ncard : ℝ) - 1 < c₁ * c₂ * Real.sqrt ((k : ℝ) + 1)) := by sorry

end LenstraIP.Hyperplanes
