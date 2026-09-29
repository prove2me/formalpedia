-- Prove2me | Theorems.Thm_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le
-- name    : ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/7665e9cb-c722-5cb4-873b-af819d75d250
-- title:
--   Width invariance in characteristic p≥ 5: r· W(j_N)=r_N· W(j)
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $N \ge 1$ be an integer with $p \nmid N$, and let $k$ be an algebraically closed field of characteristic $p$ (with decidable equality). Inside the field of Laurent series over $k$ let $F = \mathrm{modularFunctionFieldC}\,k\,N$ be the intermediate field generated over $k$ by the two series $\mathrm{jqModC}\,k = q^{-1}\cdot(\text{the reduction to }k\text{ of the integral }j\text{-numerator series})$ and its $q \mapsto q^N$ substitute $\mathrm{jqNModC}\,k\,N$; write $\tilde\jmath = \mathrm{jGeomGen}$ and $\tilde\jmath_N = \mathrm{jNGeomGen}$ for these two elements of $F$. Let $w$ be a place of $F$ over $k$, that is, a proper valuation subring of $F$ containing $k$ whose valuation ring is a principal ideal ring, with associated order function $\mathrm{ord}_w$ and residue evaluation $w.\mathrm{evalAt} : F \to k$ (the $k$-rational residue of an element of the valuation subring, and $0$ otherwise). Put $W(x) = 3$ if $x = 0$, $W(x) = 2$ if $x = 1728$ and $W(x) = 1$ otherwise, and $r(w) = \max\bigl(\mathrm{ord}_w(\tilde\jmath - \tilde\jmath(w)),0\bigr)$, $r_N(w) = \max\bigl(\mathrm{ord}_w(\tilde\jmath_N - \tilde\jmath_N(w)),0\bigr)$, where $\tilde\jmath(w) = w.\mathrm{evalAt}\,\tilde\jmath$ and likewise for $\tilde\jmath_N$. The assertion is the equality of natural numbers $r(w)\cdot W(\tilde\jmath_N(w)) = r_N(w)\cdot W(\tilde\jmath(w))$.
--
--   This is the statement that the width of a point of $X_0(N)$ in characteristic $p \ge 5$ is the same whether computed through $j$ or through $j_N$, a form of the Atkin–Lehner symmetry of widths; the two ramification numbers $r$ and $r_N$ are the ramification indices of $w$ over the $\tilde\jmath$- and $\tilde\jmath_N$-lines, vanishing at the cusps. It is used to transport widths along the two degeneracy maps, in the results [`ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le`](thm.html#ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le) and [`ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_five_le`](thm.html#ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (w : Place k ↥(modularFunctionFieldC k N)) :
    placeRamificationJ N w * jWidth (w.evalAt (jNGeomGen k N))
      = (w.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (w.evalAt (jNGeomGen k N)))).toNat
          * jWidth (w.evalAt (jGeomGen k N)) := by sorry
