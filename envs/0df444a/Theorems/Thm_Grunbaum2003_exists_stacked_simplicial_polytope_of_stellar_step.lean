-- Prove2me | Theorems.Thm_Grunbaum2003_exists_stacked_simplicial_polytope_of_stellar_step
-- name    : Grunbaum2003.exists_stacked_simplicial_polytope_of_stellar_step
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:13:07.15819+00:00
-- url     : https://prove2.me/theorems/4f0e1415-d5ef-419e-9e38-abafa9aa5ec4
-- title:
--   Inductive realization of stacked simplicial $d$-polytopes from single-facet stellar subdivision
-- statement:
--   For every dimension $d \ge 1$ and $0 \le j < d$, row $1$ of Björner's matrix $M_d$ satisfies
--
--   $$
--   M_{d,1,j+1} = \begin{cases} \binom{d}{j} & \text{if } j + 1 < d, \\ d - 1 & \text{if } j + 1 = d. \end{cases}
--   $$
--
--   Consequently, for $d \ge 4$, if every simplicial $d$-polytope $P$ admits a single-facet stellar subdivision $P'$ incrementing $f_j$ by $\binom{d}{j}$ for $j < d - 1$ and by $d - 1$ for $j = d - 1$, then iterating $n$ times starting from the standard $d$-simplex yields a simplicial $d$-polytope realizing $f_j = \binom{d+1}{j+1} + n\,M_{d,1,j+1}$ for all $n \ge 0$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §10.6, pp. 198a–198b (PDF 235–236)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_stacked_simplicial_polytope_of_stellar_step :
    (∀ {d : ℕ}, 1 ≤ d → ∀ (j : Fin d),
      gTheoremMatrix d 1 j.succ.val =
        if j.val + 1 < d then (Nat.choose d j.val : ℤ) else (d : ℤ) - 1) ∧
    (∀ (d : ℕ), 4 ≤ d →
      (∀ P : Set (Fin d → ℝ), IsSimplicialDPolytope P →
        ∃ P' : Set (Fin d → ℝ), IsSimplicialDPolytope P' ∧
          (∀ j : Fin d, j.val + 1 < d → faceCount P' j.val = faceCount P j.val + Nat.choose d j.val) ∧
          faceCount P' (d - 1) = faceCount P (d - 1) + (d - 1)) →
      ∀ n : ℕ, ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          (Nat.choose (d + 1) j.succ.val : ℤ) + (n : ℤ) * gTheoremMatrix d 1 j.succ.val) := by sorry

end Grunbaum2003
