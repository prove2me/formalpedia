-- Prove2me | Theorems.Thm_LG2021_shallow_ellipsoid_cover
-- name    : LG2021.shallow_ellipsoid_cover
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T15:20:24.209194+00:00
-- url     : https://prove2.me/theorems/07a9f510-1fd5-41c7-bd78-3b74d1cb7e38
-- title:
--   Shallow ellipsoid cover
-- statement:
--   Let $d\ge1$, let $B\in\mathbb R^{d\times d}$ be nonsingular, let $c\in\mathbb R^d$, and let $p\in\mathbb R^d$ have Euclidean norm one. Write $E(B,c)=\{c+Bu:\|u\|_2\le1\}$ and
--   $$S=\{c+Bu:\|u\|_2\le1,\ \langle p,u\rangle\le1/(2d)\}.$$
--   There are a nonsingular matrix $B'$ and a center $c'$ such that
--   $$S\subseteq E(B',c'),\qquad |\det B'|\le e^{-1/(8(d+1))}|\det B|,$$
--   and hence
--   $$\operatorname{vol}(E(B',c'))\le e^{-1/(8(d+1))}\operatorname{vol}(E(B,c)).$$
--   This unrounded shallow-cut cover, including dimension one, provides the volume contraction needed by the convex-bandit ellipsoid argument. It is a specialization of the cited shallow-cut formulas, with an explicit exponential estimate; it does not assert a finite-precision implementation bound.
-- source:
--   Martin Grötschel, László Lovász, and Alexander Schrijver, Geometric Algorithms and Combinatorial Optimization, Algorithms and Combinatorics 2, Springer, 1988, equations (3.1.16)–(3.1.17), pp. 71–72, and Lemma (3.3.21), pp. 99–100. The unrounded specialization at shallow-cut parameter 1/(2d) supplies the geometry used in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, Lemma 3, printed p. 5.

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
open Matrix MeasureTheory

theorem LG2021.shallow_ellipsoid_cover {d : ℕ} (hd : 0 < d) (c : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0)
    (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    ∃ (B' : Matrix (Fin d) (Fin d) ℝ) (c' : Fin d → ℝ), B'.det ≠ 0 ∧
      {x | ∃ u, u ⬝ᵥ u ≤ 1 ∧ p ⬝ᵥ u ≤ 1 / (2 * (d : ℝ)) ∧ x = c + B *ᵥ u} ⊆
        ModernConvex.Ellipsoids.ellipsoid B' c' ∧
      |B'.det| ≤ Real.exp (-1 / (8 * ((d : ℝ) + 1))) * |B.det| ∧
      volume (ModernConvex.Ellipsoids.ellipsoid B' c') ≤
        ENNReal.ofReal (Real.exp (-1 / (8 * ((d : ℝ) + 1)))) *
          volume (ModernConvex.Ellipsoids.ellipsoid B c) := by sorry
