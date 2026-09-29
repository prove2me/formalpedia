-- Prove2me | Theorems.Thm_ModularCurve_one_le_placeWidthChar_of_mem_ssPlaces
-- name    : ModularCurve.one_le_placeWidthChar_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/ee00dcab-45c3-523c-a3f2-20ca789fcbc2
-- title:
--   Positivity of the characteristic-q width at supersingular places
-- statement:
--   Let $q$ be a prime and $N$ a nonzero natural number with $q \nmid N$, and let $K$ be an algebraically closed field of characteristic $q$. Let $w$ be a place of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\,K\,N$, i.e. of the intermediate field of the Laurent series field $\mathrm{LaurentSeries}\,K$ generated over $K$ by the two series `jqModC K` and `jqNModC K N`; here a place is a valuation subring of that field which contains the image of $K$, is not the whole field, and is a principal ideal ring. Assume $w$ lies in $\mathrm{ssPlaces}\,q\,N\,K$, that is: $w$ is rational, satisfies `IsAffineGeomPlace K N w`, and the residue value $j(w) := w.\mathrm{evalAt}(\mathrm{jGeomGen}\,K\,N)$ of the distinguished generator lies in the set `ssJSet q K`. The conclusion is $1 \le \mathrm{placeWidthChar}\,q\,N\,w$, where $\mathrm{placeWidthChar}\,q\,N\,w$ is the natural-number quotient of $\mathrm{jWidthChar}\,q\,(j(w))$ — equal to $12$ or $1$ according as $j(w) = 0$ or not when $q = 2$, to $6$ or $1$ according as $j(w) = 0$ or not when $q = 3$, and to $\mathrm{jWidth}\,(j(w))$ otherwise — by $\mathrm{placeRamificationJ}\,N\,w = (w.\mathrm{ord}(\mathrm{jGeomGen}\,K\,N - j(w)))_{\ge 0}$. Equivalently, the latter is nonzero and at most the former.
--
--   This records that the characteristic-$q$ width attached to a supersingular place of the level-$N$ modular curve is positive, for every prime $q$ not dividing $N$, including the exceptional characteristics $2$ and $3$. It feeds the supersingular-chart bookkeeping in the genus computations for the full-level and Deligne–Rapoport model packages.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_one_le_placeWidthChar_of_mem_ssPlaces.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.one_le_placeWidthChar_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hqN : ¬ q ∣ N)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces q N K) :
    1 ≤ placeWidthChar q N w := by sorry
