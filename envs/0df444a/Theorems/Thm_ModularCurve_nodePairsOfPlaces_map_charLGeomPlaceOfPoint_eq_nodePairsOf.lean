-- Prove2me | Theorems.Thm_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf
-- name    : ModularCurve.nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/ad4a17a7-a20a-5ba3-af2e-daebdbe86d94
-- title:
--   Node pairs from places agree with node pairs from j-values
-- statement:
--   Let $K$ be a field, let $q$ be a natural number, and let $F =$ `modularFunctionFieldC K 1` be the level-one modular function field of $K$, i.e. the intermediate field of the Laurent series field $K((X))$ generated over $K$ by the $q$-expansion `jqModC K` of $j$ together with `jqNModC K 1`. Let $g$ be an element of `SemilinearAut K F`, that is a pair consisting of a ring automorphism of $F$ and a ring automorphism of $K$ compatible with the structure map $K \to F$, acting on places of $F$ over $K$ by the pointwise action. For $a \in K$ write $P_a =$ `charLGeomPlaceOfPoint K a` for the place of $F$ obtained, through the transport `charLGeomPlaceEquiv` along the isomorphism of $F$ with $K(X)$, from the finite place of $K(X)$ attached to the irreducible polynomial $X - a$. Assume $g \cdot P_a = P_{a^q}$ for every $a \in K$, and let $S$ be a finite subset of $K$. Then the image of the finite set $\{P_a : a \in S\}$ under `smulNodePair g`, which sends a place of $F$ to a pair of places, coincides with the image of $S$ under `frobNodePair q`, which produces such a pair directly from an element of $K$; that is, `nodePairsOfPlaces g` applied to the image of $S$ under $a \mapsto P_a$ equals `nodePairsOf q S`.
--
--   The statement identifies two parametrisations of the crossing pairs in the glued special fibre of a modular curve at level one: one indexed by places of the modular function field and formed using the given semilinear automorphism, the other indexed directly by the $j$-values in $S$. It is used by [`ModularCurve.exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf`](thm.html#ModularCurve.exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf), where $g$ is taken to be the arithmetic Frobenius, for which the hypothesis $g \cdot P_a = P_{a^q}$ holds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularNodes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf
    {K : Type*} [Field K] (q : ℕ) (g : SemilinearAut K (modularFunctionFieldC K 1))
    (hid : ∀ a : K, g • charLGeomPlaceOfPoint K a = charLGeomPlaceOfPoint K (a ^ q))
    (S : Finset K) :
    nodePairsOfPlaces g
        (S.map ⟨charLGeomPlaceOfPoint K, charLGeomPlaceOfPoint_injective K⟩)
      = nodePairsOf q S := by sorry
