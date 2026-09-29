-- Prove2me | Theorems.Thm_ModularCurve_sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces
-- name    : ModularCurve.sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/1b8b544c-81c4-5952-be95-ff3cb41679a0
-- title:
--   Eichler–Deuring mass formula for supersingular places at level N
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $N$ be a nonzero natural number with $q \nmid N$, and let $k$ be an algebraically closed field of characteristic $q$. Inside the Laurent series field over $k$ let $F_N =$ `modularFunctionFieldC k N` be the intermediate field generated over $k$ by the two elements `jqModC k` and `jqNModC k N`, i.e. by the reduction of the $q$-expansion of $j$ and its $N$-fold expansion. A place of $F_N$ over $k$ is, by definition, a valuation subring of $F_N$ containing the image of $k$, different from the whole field, and whose valuation ring is a principal ideal ring. Let $W$ be a finite set of such places whose members are exactly those $w$ lying in `ssPlaces q N k`, that is those $w$ which are rational (equivalently of degree one), satisfy the predicate `IsAffineGeomPlace`, and whose value $a = w(\,$`jGeomGen k N`$\,)$ at the distinguished generator belongs to the set `ssJSet q k` of supersingular $j$-invariants. For such a $w$ put $e(w) = \operatorname{ord}_w\bigl(j - a\bigr)$, the order at $w$ of `jGeomGen k N` minus the scalar $a$, and let `jWidth` $a$ be $3$ if $a = 0$, $2$ if $a = 1728$, and $1$ otherwise; the width `placeWidth N w` is the natural-number quotient of `jWidth` $a$ by $e(w)$. Then $$\sum_{w \in W} \frac{1}{\mathrm{width}(w)} = \frac{(q-1)\,\psi(N)}{12},$$ where $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ and the right-hand side is `eichlerMass N q`.
--
--   This is the Eichler–Deuring mass formula in its form on the level-$N$ modular function field: the reciprocal widths of the supersingular points in characteristic $q$ sum to the mass of an Eichler order of level $N$ in the quaternion algebra ramified at $q$ and $\infty$, normalised here as $(q-1)\psi(N)/12$. It feeds the genus and intersection computations for the special fibre of the modular curve at $q$, being cited by [`ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts`](thm.html#ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts) and [`ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq_of_liesOverPrime`](thm.html#ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq_of_liesOverPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_EichlerMass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) :
    ∑ w ∈ W, ((placeWidth N w : ℚ))⁻¹ = eichlerMass N q := by sorry
