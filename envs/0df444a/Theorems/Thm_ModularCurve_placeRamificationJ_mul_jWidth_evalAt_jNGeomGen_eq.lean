-- Prove2me | Theorems.Thm_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq
-- name    : ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/f43e8166-c2e7-5a69-a3fa-de41d70bd988
-- title:
--   Ramification over the j- and j_N-lines versus automorphism widths
-- statement:
--   Let $k$ be an algebraically closed field, let $N \ge 1$ be a natural number with $N \neq 0$ in $k$, and let $F =$ `modularFunctionFieldC k N` be the intermediate field of the Laurent series field $k((q))$ generated over $k$ by the two series `jqModC k` (the $q$-expansion $\tilde\jmath$ of $j$) and `jqNModC k N` (its $N$-fold $q$-expansion rescaling $\tilde\jmath_N$); write $\tilde\jmath =$ `jGeomGen k N` and $\tilde\jmath_N =$ `jNGeomGen k N` for the corresponding elements of $F$. Let $p$ be a place of $F$ over $k$, i.e. a valuation subring of $F$ containing $k$, different from $F$, and a principal ideal ring; for $f \in F$, $p.\mathrm{ord}\,f$ denotes the associated $\mathbb{Z}$-valued order and $p.\mathrm{evalAt}\,f \in k$ the residue of $f$ at $p$ when $f$ lies in the valuation subring (and $0$ otherwise). Put $W(a) = 3, 2, 1$ according as $a = 0$, $a = 1728$, or otherwise. Then, as natural numbers,
--   $$\bigl(p.\mathrm{ord}(\tilde\jmath - p.\mathrm{evalAt}\,\tilde\jmath)\bigr)^{+}\cdot W(p.\mathrm{evalAt}\,\tilde\jmath_N) = \bigl(p.\mathrm{ord}(\tilde\jmath_N - p.\mathrm{evalAt}\,\tilde\jmath_N)\bigr)^{+}\cdot W(p.\mathrm{evalAt}\,\tilde\jmath),$$
--   where $(\cdot)^{+}$ is truncation of an integer to $\mathbb{N}$ and the left-hand first factor is `placeRamificationJ N p`.
--
--   This is the intrinsic form of the assertion that the width of a place of the level-$N$ modular curve — the ratio of the automorphism width of its $j$-value to its ramification index over the $j$-line — is unchanged when computed through $\tilde\jmath_N$ instead of through $\tilde\jmath$, i.e. its invariance under the Fricke involution interchanging the two readings. It is used in the comparison of widths along the characteristic-dependent variant and in the multiplicativity of ramification indices and widths under restriction of places along a subfield.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq.lean

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

theorem ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (p : Place k ↥(modularFunctionFieldC k N)) :
    placeRamificationJ N p * jWidth (p.evalAt (jNGeomGen k N))
      = (p.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (p.evalAt (jNGeomGen k N)))).toNat
          * jWidth (p.evalAt (jGeomGen k N)) := by sorry
