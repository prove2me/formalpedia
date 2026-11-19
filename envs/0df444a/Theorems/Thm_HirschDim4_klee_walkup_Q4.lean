-- Prove2me | Theorems.Thm_HirschDim4_klee_walkup_Q4
-- name    : HirschDim4.klee_walkup_Q4
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:55:46.71999+00:00
-- url     : https://prove2.me/theorems/56320385-bf1a-46be-b230-757a20a1b432
-- title:
--   The Klee–Walkup polytope $Q_4$ is Hirsch-sharp ($9$ facets, distance $\ge 5$)
-- statement:
--   There is a $4$-dimensional polytope $Q_4$ with $9$ facets and two vertices at graph distance at least $5$. Since $5=9-4$, it meets the Hirsch bound with equality: it is **Hirsch-sharp**. This is the lower-bound half of $H(9,4)=5$ (Klee–Walkup 1967). $Q_4$ is the smallest non-trivial Hirsch-sharp polytope (more facets than twice its dimension) and the starting block of every known Hirsch-sharp polytope with $n>2d$. Kim and Santos give small explicit integer coordinates for the dual $Q_4^*$ (nine vectors $a,b,c,d,e,f,g,h,w$); the two tetrahedra $abcd$ and $efgh$ are at dual-graph distance $5$.
--
--   **Formalization Note.** The conclusion `∀ k<5, ¬ Reach (Hpoly a b) k u v` says the distance is at least $5$; the matching upper bound $H(9,4)\le 5$ is separate. Simplicity of $Q_4$ is not required here.
-- source:
--   Kim & Santos, An update on the Hirsch conjecture, arXiv:0907.1186, Theorem 3.8 and Section 3.3 (explicit coordinates), attributing to V. Klee & D. W. Walkup, The d-step conjecture for polyhedra of dimension d<6, Acta Math. 117 (1967), 53-78, https://doi.org/10.1007/BF02395040. Lower-bound (sharpness) half of H(9,4)=5.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace HirschDim4

theorem klee_walkup_Q4 :
    ∃ (a : Fin 9 → EuclideanSpace ℝ (Fin 4)) (b : Fin 9 → ℝ)
      (u v : EuclideanSpace ℝ (Fin 4)),
      Bornology.IsBounded (Hirsch.Hpoly a b) ∧
      SantosHirsch.Counter.IsFacetPresentation a b ∧
      u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
      v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
      ∀ k < 5, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k u v := by sorry

end HirschDim4
