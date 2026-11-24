-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_9
-- name    : Gomory69.Asymptotic.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:24:35.499817+00:00
-- url     : https://prove2.me/theorems/13bb2de2-0c16-47b4-a34a-1b9c9944d22c
-- title:
--   THEOREM 9 — The subgroup criterion and the least positive coset facet
-- statement:
--   Let $G$ be a finite Abelian group, $N\subseteq G\setminus\{0\}$, $g_0\in G$, $h\in N$ and $K=\langle N\setminus\{h\}\rangle$. Then
--   $$t(h)\ge0\text{ is a facet of }P(G,N,g_0)\quad\Longleftrightarrow\quad g_0\in K.$$
--   If the group equation has a nonnegative integer solution and $g_0\notin K$, there is a least positive integer $p$ with $g_0-ph\in K$, and
--   $$t(h)\ge p\text{ is a facet of }P(G,N,g_0).$$
--   The leastness is among all strictly positive coset indices. Reachability is required only for the second conclusion; the equivalence keeps its entire domain.
--
--   This determines both coordinate nonnegativity facets and their positive-coset replacements.
--
--   Differences from the source:
--   - reading: the positive-coset assertion is stated after the subgroup criterion → the positive branch explicitly assumes a solution exists; reason: p. 472 explicitly says if P(G,N,g0) is not empty; without reachability the coset need not exist
--   - encoding: p is the smallest positive coset index → existence, positivity, coset membership and comparison against every other positive index; reason: this avoids a default minimum for an empty set
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 471, THEOREM 9

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_Supplement_Subgroup

namespace Gomory69.Asymptotic.Supplement

theorem theorem_9 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : 0 ∉ N) (g₀ : G) (h : N) :
    (Gomory69.MasterFaces.IsFace N g₀ (fun g => if g = h then 1 else 0) 0 ↔
      g₀ ∈ deletedSubgroup N h) ∧
    ((∃ t : N → ℕ, Gomory69.MasterFaces.GroupSolution N g₀ t) →
      g₀ ∉ deletedSubgroup N h →
      ∃ p : ℕ, 0 < p ∧ g₀ - p • (h : G) ∈ deletedSubgroup N h ∧
        (∀ q : ℕ, 0 < q → g₀ - q • (h : G) ∈ deletedSubgroup N h → p ≤ q) ∧
        Gomory69.MasterFaces.IsFace N g₀ (fun g => if g = h then 1 else 0) (p : ℝ)) := by sorry

end Gomory69.Asymptotic.Supplement
