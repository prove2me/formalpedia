-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_remark_3_4_merge
-- name    : KleeWalkup67.FiveStep.remark_3_4_merge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:50.377371+00:00
-- url     : https://prove2.me/theorems/1b0f0385-bc3c-4bef-9b9b-36c94682976e
-- title:
--   Remark after 3.4 — two adjacent terms of a facial path in a simple figure can be merged
-- statement:
--   Let $(P,x,y)$ be a $d$-dimensional simple Dantzig figure that admits a $(k_1,\dots,k_r)$-path from $x$ to $y$. If two adjacent terms $k_i,k_{i+1}$ satisfy $k_i+k_{i+1}\le d$, then $P$ also admits a path from $x$ to $y$ of type
--   $$(k_1,\dots,k_{i-1},\,k_i+k_{i+1},\,k_{i+2},\dots,k_r).$$
--
--   The paper: "It is a consequence of 1.5 that if a simple figure $(P,x,y)$ admits a $(k_1,\dots,k_r)$-path from $x$ to $y$ then it also admits a $(k'_1,\dots,k'_s)$-path from $x$ to $y$, where the sequence $(k'_1,\dots,k'_s)$ is obtained from $(k_1,\dots,k_r)$ by removing adjacent terms and replacing them by a single term equal to their sum." Repeating the single merge gives the general statement.
--
--   **Formalization Note** The hypothesis $k_i+k_{i+1}\le d$ is added: a $d$-polyhedron has no face of dimension above $d$, so without it the remark fails (e.g. a $(d,d)$-path never becomes a $(2d)$-path). The paper's "simple figure" is read as a simple Dantzig figure, the setting of §3. The type is a list `l₁ ++ p :: q :: l₂`, merged to `l₁ ++ (p + q) :: l₂`.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), pp. 66–67, remark following 3.4 PROPOSITION

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- Remark after 3.4, pp. 66–67: in a simple Dantzig figure, two adjacent terms `p, q` of the
type of a facial path from `x` to `y` can be replaced by their sum (provided `p + q ≤ d`, so
that a face of that dimension can exist). -/
theorem remark_3_4_merge {d : ℕ}
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (l₁ l₂ : List ℕ) (p q : ℕ) (hpq : p + q ≤ d)
    (hpath : IsFacialPath a b (l₁ ++ p :: q :: l₂) x y) :
    IsFacialPath a b (l₁ ++ (p + q) :: l₂) x y := by sorry

end KleeWalkup67.FiveStep
