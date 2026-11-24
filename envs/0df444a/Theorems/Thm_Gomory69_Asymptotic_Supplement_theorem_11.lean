-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_11
-- name    : Gomory69.Asymptotic.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:25:00.78587+00:00
-- url     : https://prove2.me/theorems/18517504-9ad6-4114-8cb5-11cab2d35e45
-- title:
--   THEOREM 11 — Persistence of a facet along a shortest path
-- statement:
--   Let $G$ be a finite Abelian group and $N\subseteq G\setminus\{0\}$. Let $(\pi,\pi_0)$ be a facet of $P(G,N,g_0)$ with $\pi_0>0$. Suppose a shortest path from $0$ to $h$ has multiplicity vector $t$, and a prefix to $g_0$ has multiplicity vector $s\le t$. Then
--   $$\left(\pi,\ \sum_{g\in N}\pi(g)t(g)\right)\text{ is a facet of }P(G,N,h).$$
--   The new constant is precisely the shortest-path length, not necessarily the old constant $\pi_0$.
--
--   This gives the same normal a geometric meaning at other targets reached through the original one.
--
--   Differences from the source:
--   - encoding: a shortest path from 0 through g0 to h → t is shortest to h and contains a nonnegative integer subvector s representing g0; reason: in this translation-invariant Abelian graph the arcs can be ordered with s first, as p. 472 explains
--   - reading: there exists a constant pi0(h) → the constant is the length of the specified shortest path; reason: the final sentence of the proof on p. 474 identifies that constant
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 474, THEOREM 11

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.Asymptotic.Supplement

theorem theorem_11 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : 0 ∉ N) (g₀ h : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : Gomory69.MasterFaces.IsFace N g₀ π π₀)
    (t s : N → ℕ) (ht : Gomory69.MasterFaces.IsShortest N h π t)
    (hs : Gomory69.MasterFaces.GroupSolution N g₀ s) (hst : ∀ g, s g ≤ t g) :
    Gomory69.MasterFaces.IsFace N h π
      (Gomory69.MasterFaces.dot π (Gomory69.MasterFaces.castSolution t)) := by sorry

end Gomory69.Asymptotic.Supplement
