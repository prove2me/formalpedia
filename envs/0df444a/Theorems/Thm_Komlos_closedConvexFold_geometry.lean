-- Prove2me | Theorems.Thm_Komlos_closedConvexFold_geometry
-- name    : Komlos.closedConvexFold_geometry
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:55:05.703626+00:00
-- url     : https://prove2.me/theorems/b1114bb2-9c0b-42a4-88d8-5d7bd06760e8
-- title:
--   Compactness, convexity, and translate containment of the closed fold
-- statement:
--   Let $K\subseteq\mathbb R^m$ be compact and convex and let $u\in\mathbb R^m$. For the closed fold $F_u(K)$ defined by the retained fibers of length at least $2\|u\|$,
--   $$F_u(K)\text{ is compact and convex},\qquad F_u(K)\subseteq(K-u)\cup(K+u).$$
--   This assertion holds for every vector $u$, including zero, and requires no Gaussian measure hypothesis. It supplies the geometric part of the folding step in vector balancing.
-- source:
--   Shashwat Garg, Algorithms for Combinatorial Discrepancy, TU Eindhoven PhD thesis (2018), Chapter 3, Definition 14 and following convexity observation, printed p. 18. https://pure.tue.nl/ws/files/107722737/20181010_Garg.pdf . The closed-fold definition expresses the retained fibers using endpoints y,y+2u; compactness is recorded explicitly for compact K.

import Definitions.Def_Komlos_convex_fold
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open Set MeasureTheory ProbabilityTheory
open scoped Pointwise
set_option autoImplicit false

theorem Komlos.closedConvexFold_geometry (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ K) (hcomp : IsCompact K) (u : EuclideanSpace ℝ (Fin m)) :
    Convex ℝ (Komlos.closedConvexFold m K u) ∧
      IsCompact (Komlos.closedConvexFold m K u) ∧
      ∀ x ∈ Komlos.closedConvexFold m K u, x + u ∈ K ∨ x - u ∈ K := by sorry
