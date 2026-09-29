-- Prove2me | Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
-- name    : ModularCurve.placeRamificationJ_dvd_jWidth_of_ord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/d675577e-27ff-54e7-b81b-92c35db8b143
-- title:
--   Ramification over the j-line divides the j-width
-- statement:
--   Let $q$ be a prime with $5 \le q$, let $N \ge 1$, and suppose $q \nmid N$. Let $K$ be an algebraically closed field of characteristic $q$, and let $F =$ `modularFunctionFieldC K N` be the intermediate field of the Laurent series field $K((\mathsf q))$ generated over $K$ by the two series `jqModC K` and `jqNModC K N` (the $q$-expansion of $j$ and its $N$-fold expansion). Let $w$ be a place of $F/K$, that is, a valuation subring of $F$ containing $\operatorname{im}(K \to F)$, different from $F$ itself and a principal ideal ring. Write $a =$ `w.evalAt (jGeomGen K N)` for the value at $w$ of the distinguished generator $\bar\jmath =$ `jqModC K`, obtained by reducing $\bar\jmath$ in the residue field of $w$ and pulling back along an inverse of $K \to$ residue field (and set to $0$ if $\bar\jmath$ is not in the valuation subring). Assume the integer $e_w = (\operatorname{ord}_w(\bar\jmath - a))_{\ge 0}$, i.e. `placeRamificationJ N w`, is positive. Then $e_w$ divides `jWidth a`, which is $3$ if $a = 0$, $2$ if $a = 1728$, and $1$ otherwise.
--
--   This is the statement that the ramification index, at a place centred at a point $a$ of the affine $j$-line, of the covering of the $j$-line by the level-$N$ modular function field in characteristic $q \nmid N$ divides the extra-automorphism width of $a$ (half the order of $\operatorname{Aut}$ of an elliptic curve with $j$-invariant $a$). It underlies the subsequent definition and computation of place widths on the modular curve, used in the divisor-theoretic and Hecke-theoretic analysis of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos.lean

import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.placeRamificationJ_dvd_jWidth_of_ord_pos
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N)
    {w : Place K (modularFunctionFieldC K N)}
    (hw : 0 < placeRamificationJ N w) :
    placeRamificationJ N w ∣ jWidth (w.evalAt (jGeomGen K N)) := by sorry
