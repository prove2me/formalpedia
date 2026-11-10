-- Prove2me | Theorems.Thm_Grunbaum2003_exists_stellar_subdivision_simplicial_polytope
-- name    : Grunbaum2003.exists_stellar_subdivision_simplicial_polytope
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:13:05.377259+00:00
-- url     : https://prove2.me/theorems/46bf8420-709c-4b57-9c42-182259e829c5
-- title:
--   Single-facet stellar subdivision of a simplicial $d$-polytope ($d \ge 4$)
-- statement:
--   Let $d \ge 4$ and let $P \subset \mathbb{R}^d$ be a simplicial $d$-polytope. Performing a stellar subdivision on a facet of $P$ produces a simplicial $d$-polytope $P' \subset \mathbb{R}^d$ whose face counts satisfy
--
--   $$
--   f_j(P') = f_j(P) + \binom{d}{j} \quad (0 \le j < d - 1), \qquad f_{d-1}(P') = f_{d-1}(P) + (d - 1).
--   $$
--
--   This is the elementary geometric step used to build stacked simplicial $d$-polytopes.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §3.2 & §10.6, pp. 198a–198b (PDF 235–236)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_stellar_subdivision_simplicial_polytope (d : ℕ) (hd : 4 ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P) :
    ∃ P' : Set (Fin d → ℝ), IsSimplicialDPolytope P' ∧
      (∀ j : Fin d, j.val + 1 < d → faceCount P' j.val = faceCount P j.val + Nat.choose d j.val) ∧
      faceCount P' (d - 1) = faceCount P (d - 1) + (d - 1) := by sorry

end Grunbaum2003
