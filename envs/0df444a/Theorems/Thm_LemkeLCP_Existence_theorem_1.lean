-- Prove2me | Theorems.Thm_LemkeLCP_Existence_theorem_1
-- name    : LemkeLCP.Existence.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:03:57.267064+00:00
-- url     : https://prove2.me/theorems/b0a6fa15-958a-49e5-b0d9-1bf99a0c6c82
-- title:
--   Theorem 1, p. 3 — for non-degenerate Z, Zₛ is empty or a disjoint union of adjacency paths whose end-points are the equilibrium points
-- statement:
--   Let $M$ be a real square matrix of order $n$ and $q\in\mathbb R^n$, and let $Z=\{z\ge 0 : w=Mz-q\ge0\}$ be non-degenerate. Fix an index $s$ and let $Z_s=\{z\in Z: z^{\mathsf T}w=z_sw_s\}$ be the set of points of $Z$ at which every complementary product except possibly the $s$-th vanishes. Then either $Z_s=\emptyset$, or there is a family $\mathcal P$ of adjacency paths of $Z$ such that
--
--   1. the paths of $\mathcal P$ (as point sets) are pairwise disjoint,
--   2. their union is $Z_s$, and
--   3. the set $S$ of equilibrium points of $Z$ is exactly the set of end-points of the paths of $\mathcal P$:
--   $$S=\{z : z \text{ is an end-point of some path } \mathcal C\in\mathcal P\}.$$
--
--   This is the combinatorial core of the paper: following an adjacency path inside $Z_s$ from one end leads either to an equilibrium point or off along a ray, and it is the basis of the parity count of Theorem 2 and of Lemke's complementary pivoting algorithm.
--
--   **Formalization Note** An adjacency path is a class of closed edges (closures of open edges); its point set is the union of the class. An end-point of a path is an extreme point of $Z$ lying on exactly one edge of the class. Non-degeneracy is Def. 3 as formalized in the definitions file.
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, p. 3, Theorem 1

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (hnd : NonDegenerate M q) (s : ι) :
    Zs M q s = ∅ ∨
      ∃ 𝔓 : Set (Set (Set (ι → ℝ))),
        (∀ 𝒞 ∈ 𝔓, IsAdjacencyPath M q 𝒞) ∧
        𝔓.PairwiseDisjoint (fun 𝒞 => ⋃₀ 𝒞) ∧
        (⋃ 𝒞 ∈ 𝔓, ⋃₀ 𝒞) = Zs M q s ∧
        S M q = {z | ∃ 𝒞 ∈ 𝔓, IsPathEndPoint M q 𝒞 z} := by sorry

end LemkeLCP.Existence
