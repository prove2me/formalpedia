-- Prove2me | Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
-- name    : ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/1a2cc167-a876-54a7-ad5a-a25bdd71cce7
-- title:
--   Ramification over the j-line divides the j-width
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $N$ be a nonzero natural number with $q \nmid N$, and let $K$ be an algebraically closed field of characteristic $q$. Work inside the field $\mathrm{modularFunctionFieldC}\ K\ N$, the intermediate field of the Laurent series field $K((t))$ generated over $K$ by the two series $\mathrm{jqModC}\ K$ and $\mathrm{jqNModC}\ K\ N$, and write $\tilde{j} = \mathrm{jGeomGen}\ K\ N$ for the element given by $\mathrm{jqModC}\ K$. Let $w$ be a place of this field over $K$, that is, a valuation subring containing the image of $K$, different from the whole field, and a principal ideal ring; let $w.\mathrm{evalAt}$ denote evaluation, sending an element of the valuation subring to the preimage in $K$ of its residue class and sending elements outside it to $0$. Assume $w$ lies in $\mathrm{ssPlaces}\ q\ N\ K$, i.e. $w$ satisfies `Place.IsRational` and `IsAffineGeomPlace K N`, and $w.\mathrm{evalAt}\ \tilde{j}$ lies in `ssJSet q K`. Then the natural number $\mathrm{placeRamificationJ}\ N\ w$, the truncation to $\mathbb{N}$ of the order of vanishing at $w$ of $\tilde{j} - w.\mathrm{evalAt}(\tilde{j})$, divides $\mathrm{jWidth}(w.\mathrm{evalAt}\ \tilde{j})$, which by definition is $3$ at $j = 0$, $2$ at $j = 1728$, and $1$ otherwise.
--
--   The statement is the divisibility underlying the place width at a supersingular point of the level-$N$ modular curve in characteristic $q \ge 5$: the ramification index of $w$ over the $j$-line divides the width of the $j$-invariant of its centre, so that the truncating division defining the width is exact. It is used in the computation of place widths and crossing exponents at supersingular places, and through these in the genus formulas for the level-$N$ and level-$H$ modular function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces q N K) :
    placeRamificationJ N w ∣ jWidth (w.evalAt (jGeomGen K N)) := by sorry
