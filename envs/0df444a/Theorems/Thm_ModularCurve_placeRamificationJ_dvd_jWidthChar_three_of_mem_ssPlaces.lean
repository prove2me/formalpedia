-- Prove2me | Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
-- name    : ModularCurve.placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/d54665cd-968e-50c3-b89e-aea7f064a420
-- title:
--   Ramification over the j-line divides the width at supersingular places
-- statement:
--   Let $N\ge 1$ and let $K$ be an algebraically closed field of characteristic $3$, and assume $3\nmid N$. Work in the level-$N$ modular function field `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two series `jqModC K` $=q^{-1}\cdot\overline{\,\mathrm{jNum}\,}$ (the $q$-expansion of $j$, with integral coefficients reduced into $K$) and its $N$-fold substitute `jqNModC K N` $=$ `qExpand K N (jqModC K)`. Let $w$ be a place of this field over $K$, i.e. a valuation subring containing $\mathrm{algebraMap}\,K$, different from the whole field and a principal ideal ring, and suppose $w$ lies in `ssPlaces 3 N K`: that is, $w$ is rational in the sense of `Place.IsRational`, it satisfies the predicate `IsAffineGeomPlace K N w`, and the value $w.\mathrm{evalAt}$ of the generator `jGeomGen K N` $=$ `jqModC K` at $w$ — the element of $K$ whose image in the residue field is the residue of the generator when it is $w$-integral, and $0$ otherwise — lies in the set `ssJSet 3 K`. Write $j_0 := w.\mathrm{evalAt}(\mathrm{jGeomGen}\,K\,N)$. Then $\mathrm{ord}_w\bigl(\mathrm{jGeomGen}\,K\,N-\mathrm{algebraMap}\,K\,j_0\bigr)$, truncated to a natural number, divides `jWidthChar 3` $j_0$, which equals $6$ if $j_0=0$ and $1$ otherwise.
--
--   This is the statement that at a supersingular point of the level-$N$ modular curve in characteristic $3$ (level prime to $3$) the ramification index of the map to the $j$-line divides the automorphism width $6$ attached to the supersingular $j$-invariant $j=0$, the remaining cases being unramified. It is used in the analysis of place specialisations and prolongation tuples, where crossing exponents at supersingular places are matched with the characteristic-adjusted widths.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces.lean

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

theorem ModularCurve.placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
    {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K 3] [IsAlgClosed K] [DecidableEq K]
    (h3N : ¬ 3 ∣ N)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces 3 N K) :
    placeRamificationJ N w ∣ jWidthChar 3 (w.evalAt (jGeomGen K N)) := by sorry
