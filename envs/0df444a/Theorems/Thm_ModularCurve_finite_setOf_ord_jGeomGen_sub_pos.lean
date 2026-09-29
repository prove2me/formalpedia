-- Prove2me | Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
-- name    : ModularCurve.finite_setOf_ord_jGeomGen_sub_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/8459e765-844e-522a-83f3-66e681a9fe47
-- title:
--   Finiteness of zeros of j - a on the level-N modular function field
-- statement:
--   Let $K$ be a field and $N$ a positive integer. Inside the Laurent series field $K((q))$ put $\bar j =$ `jqModC K`, the series $q^{-1}$ times the image in $K$ of the integral power series $E_4^3 \cdot \eta^{-24}$-type numerator `jNum`, and $\bar j_N =$ `jqNModC K N`, obtained from $\bar j$ by multiplying all exponents by $N$ (substituting $q \mapsto q^N$); let `modularFunctionFieldC K N` be the intermediate field $K(\bar j, \bar j_N)$ of $K((q))$, and let `jGeomGen K N` be the element $\bar j$ of that field. Assume that $\bar j_N$ is separable over the subfield $K(\bar j)$, i.e. its minimal polynomial over $K(\bar j)$ is separable. Let $a \in K$. Then the set of places $w$ of $K(\bar j, \bar j_N)$ over $K$ — valuation subrings of $K(\bar j,\bar j_N)$ that contain the image of $K$, are proper, and are principal ideal rings — with $\mathrm{ord}_w(\bar j - a) > 0$, where $\mathrm{ord}_w$ is minus the logarithm of the associated height-one adic valuation, is finite.
--
--   This is the statement that the modular invariant $\bar j$ takes the value $a$ at only finitely many places of the geometric modular function field of level $N$, equivalently that only finitely many places lie over the zero of $j - a$ on the $j$-line. It underlies the counting of points and places used in the genus and special-fibre computations for the modular curves of level $N$ and for the curves attached to subgroups $H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos.lean

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.finite_setOf_ord_jGeomGen_sub_pos (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N))
    (a : K) :
    {w : Place K (modularFunctionFieldC K N) |
      0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)}.Finite := by sorry
