-- Prove2me | Theorems.Thm_ModularCurve_placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces
-- name    : ModularCurve.placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/a3b941a2-be1e-55ed-a8af-9762130207ad
-- title:
--   Ramification and characteristic-q widths at a supersingular place
-- statement:
--   Let $q$ be a prime, $N$ a nonzero natural number, and $K$ an algebraically closed field of characteristic $q$ with decidable equality. Let $F =$ `modularFunctionFieldC K N` be the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two series `jqModC K` and `jqNModC K N`, and let $\tilde\jmath =$ `jGeomGen K N` and $\tilde\jmath_N =$ `jNGeomGen K N` be the elements of $F$ given by these two series. Assume $q \nmid N$, and let $w$ be a place of $F$ over $K$ (a valuation subring of $F$, not all of $F$, containing $\operatorname{im}(K \to F)$ and a principal ideal ring) lying in `ssPlaces q N K`, that is, $w$ is rational, satisfies `IsAffineGeomPlace K N w`, and its value $a = w(\tilde\jmath)$ obtained by reducing to the residue field and pulling back along $K \to \kappa(w)$ lies in `ssJSet q K`. Write $b = w(\tilde\jmath_N)$ for the analogous value of $\tilde\jmath_N$, and $e = \operatorname{ord}_w(\tilde\jmath - a)$, $e_N = \operatorname{ord}_w(\tilde\jmath_N - b)$ for the orders of vanishing at $w$ (truncated to $\mathbb{N}$; the first of these is `placeRamificationJ N w`). Then $$e \cdot W_q(b) = e_N \cdot W_q(a),$$ where $W_q(x) =$ `jWidthChar q x` equals $12$ or $1$ according as $x = 0$ or not when $q = 2$, equals $6$ or $1$ according as $x = 0$ or not when $q = 3$, and otherwise equals $3$, $2$, $1$ according as $x = 0$, $x = 1728$, or neither.
--
--   This is the compatibility between the two readings of the ramification of the level-$N$ modular curve over the $j$-line at a supersingular place, weighted by the characteristic-$q$ widths of the two $j$-values attached to the place; classically the two products both count the stabiliser of the kernel of the corresponding cyclic $N$-isogeny inside the automorphism group modulo $\pm 1$. It is used in the comparison of ramification indices and width characters along a degeneracy pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hqN : ¬ q ∣ N)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces q N K) :
    placeRamificationJ N w * jWidthChar q (w.evalAt (jNGeomGen K N))
      = (w.ord (jNGeomGen K N - algebraMap K (modularFunctionFieldC K N)
          (w.evalAt (jNGeomGen K N)))).toNat * jWidthChar q (w.evalAt (jGeomGen K N)) := by sorry
