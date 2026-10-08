-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_remark_3_4_one_dm2_one
-- name    : KleeWalkup67.FiveStep.remark_3_4_one_dm2_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:06.919459+00:00
-- url     : https://prove2.me/theorems/8edc8fe2-82ac-42f1-8a8a-093455c7f883
-- title:
--   Remark after 3.4 and p. 68 — bounded simple Dantzig figures of dimension d ≥ 2 possess (1, d − 2, 1)-paths
-- statement:
--   Let $d\ge 2$ and let $(P,x,y)$ be a $d$-dimensional bounded simple Dantzig figure. Then $P$ admits a $(1,d-2,1)$-path from $x$ to $y$: an edge $f$ through $x$, a $(d-2)$-face $Q$ and an edge $g$ through $y$ with $f\cap Q\ne\emptyset\ne Q\cap g$.
--
--   The paper: "Thus, for example, 3.5 implies that bounded simple Dantzig figures $(P,x,y)$ of dimension $d$ possess $(1,d-2,1)$-paths from $x$ to $y$" (p. 67), and, opening §4, "By 3.4 there is always a $(1,d-2,1)$-path $(f,Q,g)$ from $x$ to $y$ in such a figure" (p. 68).
--
--   This is the step that reduces the bounded $d$-step conjecture to a property of the $(d-2)$-face $Q$ (4.1).
--
--   **Formalization Note** The printed "3.5 implies" is a slip for 3.4: 3.5 concerns the ef-diagram, and the consequence is 3.4(b) with $k_2=d-3$, $k_4=1$ merged in the middle, as p. 68 says. The paper states the claim for every dimension $d$; the Lean asks only $d\ge2$, the range in which a $(1,d-2,1)$-path makes sense (natural-number subtraction would otherwise give $d-2=0$). The derivation from 3.4(b) covers $d\ge4$ (positive $k_2,k_4$); for $d=3$ the claim is 3.4(a) with $k_1=k_3=1$, and for $d=2$ the figure is a quadrilateral. The paper applies it at $d=5$.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), p. 67, remark following 3.4 ("3.5" read as 3.4); p. 68, opening of §4

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- Remark after 3.4, p. 67 (with the printed "3.5" read as 3.4), and p. 68: a bounded simple
Dantzig figure of dimension `d ≥ 2` admits a `(1, d − 2, 1)`-path from `x` to `y`. -/
theorem remark_3_4_one_dm2_one {d : ℕ} (hd : 2 ≤ d)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (hB : Bornology.IsBounded (Hirsch.Hpoly a b)) :
    IsFacialPath a b [1, d - 2, 1] x y := by sorry

end KleeWalkup67.FiveStep
