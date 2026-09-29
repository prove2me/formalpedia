-- Prove2me | Theorems.Thm_ModularCurve_natCard_componentGroup_widthOfPlaces_eq_eisensteinNumerator
-- name    : ModularCurve.natCard_componentGroup_widthOfPlaces_eq_eisensteinNumerator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/e8207429-9ddb-5c26-adeb-7d08cd598a12
-- title:
--   Component group at p has order num((p-1)/12)
-- statement:
--   Let $p$ be a prime and $K$ an algebraically closed field of characteristic $p$. Let $W$ be a finite set of places of the level-one modular function field `modularFunctionFieldC K 1` over $K$ — the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the $q$-expansion `jqModC K` and its level-one companion — where a place is a valuation subring containing the image of $K$, proper, and a principal ideal ring. Assume $W$ consists exactly of the supersingular places, i.e. $w \in W$ if and only if $w$ satisfies `IsSupersingularPlace p 1 K`. Let $e$ be any $\mathbb{N}$-valued function on places such that for every $w \in W$ the value $e(w)$ is the $j$-width of the residue value $w(\mathrm{ev})$ of the generator `jGeomGen K 1` at $w$ (the residue class pulled back to $K$, and $0$ if the generator is not integral at $w$), that is, $3$ if this value is $0$, $2$ if it is $1728$, and $1$ otherwise. Then the component group associated with the width function $s \mapsto e(s_1)$ on the finite index set `nodePairsOfPlaces (arithFrobC p K 1) W` of node pairs attached to $W$ and the coefficientwise arithmetic Frobenius on `modularFunctionFieldC K 1` (the quotient of the $\mathbb{Z}$-dual of the character lattice, the kernel of the total-degree map, by the image of the Gram map of the width pairing) is finite of cardinality $(p-1)/\gcd(p-1,12)$, the numerator of $(p-1)/12$.
--
--   This is the Mazur–Rapoport computation of the order of the Néron component group of $J_0(p)$ at $p$, read off the dual graph of the Deligne–Rapoport fibre, here stated for an arbitrary width function agreeing with the $j$-width on the supersingular places, the indexing convention used downstream. It is invoked in the construction of extensions of component homomorphisms out of the Deligne–Rapoport model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_componentGroup_widthOfPlaces_eq_eisensteinNumerator.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.natCard_componentGroup_widthOfPlaces_eq_eisensteinNumerator
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (W : Finset (Place K (modularFunctionFieldC K 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 K)
    (e : Place K (modularFunctionFieldC K 1) → ℕ)
    (he : ∀ w ∈ W, e w = jWidth (w.evalAt (jGeomGen K 1))) :
    Nat.card (componentGroup (widthOfPlaces (arithFrobC p K 1) W e)) = eisensteinNumerator p := by sorry
