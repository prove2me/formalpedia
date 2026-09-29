-- Prove2me | Theorems.Thm_ModularCurve_weightFloor_eq_of_isAffineGeomPlace
-- name    : ModularCurve.weightFloor_eq_of_isAffineGeomPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/f6c67916-a2e2-5813-8d88-6777d0807cca
-- title:
--   Weight-2m floor at an affine geometric place
-- statement:
--   Let $p\ge 5$ be a prime, let $N$ be a nonzero natural number with $p\nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Let $m$ be a natural number and let $x$ be a place of $F=$ `modularFunctionFieldC K N`, the intermediate field of the Laurent series field over $K$ generated over $K$ by $j=$ `jqModC K` and by `jqNModC K N` (the $q$-expansion of $j$ rescaled by $N$); here a `Place` is a valuation subring of $F$ containing the image of $K$, distinct from $F$, and a principal ideal ring. Assume `IsAffineGeomPlace K N x`, i.e. both `jGeomGen K N` $=j$ and `jNGeomGen K N` lie in the valuation subring of $x$. Write $a =$ `x.evalAt (jGeomGen K N)` for the value of $j$ at $x$ (the element of $K$ whose residue class is that of $j$), $w =$ `jWidth a`, which is $3$ if $a=0$, $2$ if $a=1728$ and $1$ otherwise, $e =$ `placeRamificationJ N x` $=\mathrm{ord}_x\bigl(j-a\bigr)$ truncated to $\mathbb N$, and `placeWidth N x` $= w/e$ (natural-number division). Then `weightFloor K N m x`, namely
--   $$\bigl[\mathrm{ord}_x j>0\bigr]\,\bigl\lfloor 2m\,\mathrm{ord}_x j/3\bigr\rfloor+\bigl[\mathrm{ord}_x (j-1728)>0\bigr]\,\bigl\lfloor m\,\mathrm{ord}_x (j-1728)/2\bigr\rfloor+\bigl[\mathrm{ord}_x j<0\bigr]\,m\,\mathrm{ord}_x j,$$
--   equals the integer quotient of $m\,(w-1)$ by `placeWidth N x`.
--
--   This identifies, at places lying over the affine $j$-line, the local clause of the weight-$2m$ floor divisor on the modular curve of level $N$ in characteristic $p$ with the expression $\lfloor m(w-1)/(w/e)\rfloor$ built from the elliptic-point width $w\in\{1,2,3\}$ and the ramification index $e$ of $x$ over the $j$-line. It feeds the bookkeeping of weight-$2m$ forms used in the characteristic-$p$ Hecke-operator constructions on the special fibre, such as [`ModularCurve.SSHeckeV2.liftFun_spec`](thm.html#ModularCurve.SSHeckeV2.liftFun_spec).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_weightFloor_eq_of_isAffineGeomPlace.lean

import Mathlib
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.weightFloor_eq_of_isAffineGeomPlace
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (m : ℕ) (x : Place K (modularFunctionFieldC K N)) (hx : IsAffineGeomPlace K N x) :
    weightFloor K N m x
      = ((m : ℤ) * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1)) / (placeWidth N x : ℤ) := by sorry
