-- Prove2me | Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
-- name    : ModularCurve.placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/2d3d04ec-5e61-5aa5-ae54-d270f0e65e1d
-- title:
--   Ramification over the j-line divides the char-2 width
-- statement:
--   Let $N\ge 1$ be a natural number with $2\nmid N$, and let $K$ be an algebraically closed field of characteristic $2$. Work in the function field $F=$ `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two series `jqModC K` (the $q$-expansion $q^{-1}\cdot(\text{power series }\mathrm{jNum})$ of the modular invariant $j$) and `jqNModC K N` $=$ `qExpand K N (jqModC K)` (its image under $q\mapsto q^{N}$); write $\tilde{j} =$ `jGeomGen K N` for `jqModC K` viewed in $F$. Let $w$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing $K$, distinct from $F$ itself, and a principal ideal ring, and assume $w$ lies in `ssPlaces 2 N K`: $w$ satisfies `Place.IsRational` and `IsAffineGeomPlace K N`, and its centre value $j_{0} = w.\mathrm{evalAt}\,\tilde{j}$ — the residue of $\tilde{j}$ in the residue field, transported back to $K$ along the inverse of $K\to$ residue field, or $0$ if $\tilde{j}$ is not in the valuation subring — belongs to `ssJSet 2 K`. The conclusion is that `placeRamificationJ N w`, the natural-number truncation of the order $w.\mathrm{ord}\,(\tilde{j}-j_{0})$, divides `jWidthChar 2 j₀`, which by definition is $12$ if $j_{0}=0$ and $1$ otherwise.
--
--   This is the divisibility underlying the local description of the map to the $j$-line at a supersingular point of the level-$N$ modular curve in characteristic $2$, where the relevant $j$-invariant is $0$ and the quantity $12$ records the automorphisms of the corresponding elliptic curve up to sign. It feeds the bookkeeping of widths and crossing exponents at special fibres, being used in the results on prolongation tuples and place specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
    {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K] [DecidableEq K]
    (h2N : ¬ 2 ∣ N)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces 2 N K) :
    placeRamificationJ N w ∣ jWidthChar 2 (w.evalAt (jGeomGen K N)) := by sorry
