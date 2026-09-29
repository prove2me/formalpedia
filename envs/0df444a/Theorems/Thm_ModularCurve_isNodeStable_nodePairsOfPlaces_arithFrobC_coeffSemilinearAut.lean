-- Prove2me | Theorems.Thm_ModularCurve_isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut
-- name    : ModularCurve.isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/cf51c85b-6873-5126-acb0-72cf21cf9ea0
-- title:
--   Coefficient automorphisms stabilise the supersingular node pairs
-- statement:
--   Fix a natural number $q$ that is prime and a nonzero natural number $N$, and let $K$ be an algebraically closed field of characteristic $q$. Work inside the modular function field `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((\mathsf q))$ generated over $K$ by the two series `jqModC K` and `jqNModC K N`; its places are the objects of `Place K (modularFunctionFieldC K N)`, that is, valuation subrings of the field which contain the image of $K$, are not the whole field, and are principal ideal rings. Let $W$ be a finite set of such places, assumed (hypothesis `hW`) to consist of exactly the members of `ssPlaces q N K`, i.e. of those places $w$ for which $w$ is rational, `IsAffineGeomPlace K N w` holds, and the value `w.evalAt (jGeomGen K N)` belongs to `ssJSet q K`. Let $\tau$ be a ring automorphism of $K$. Form the finite set of pairs `nodePairsOfPlaces (arithFrobC q K N) W`, the image of $W$ under the injective map `smulNodePair` attached to `arithFrobC q K N`, which couples a place with its translate under the semilinear automorphism raising all $\mathsf q$-expansion coefficients to the $q$-th power. The conclusion is `SemilinearAut.IsNodeStable` for this set of pairs and the semilinear automorphism `coeffSemilinearAut N τ` acting on coefficients through $\tau$: for every pair $s$ in the set, the pair obtained by applying `coeffSemilinearAut N τ` to both entries of $s$ again lies in the set.
--
--   The pairs in `nodePairsOfPlaces (arithFrobC q K N) W` are the double points of the special fibre at $q$, where a supersingular place of one component is glued to its Frobenius translate on the other; the theorem records that this gluing datum is invariant under every automorphism of the algebraically closed constant field acting on $\mathsf q$-expansion coefficients. It is used in the construction of the Néron-model objects and their toric parts, and in the comparison of Hecke and Frobenius actions on the relative Picard group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut
    (q N : ℕ) [NeZero N] [Fact q.Prime] (K : Type*) [Field K] [CharP K q] [IsAlgClosed K]
    [DecidableEq K] (W : Finset (Place K (modularFunctionFieldC K N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N K) (τ : K ≃+* K) :
    SemilinearAut.IsNodeStable (nodePairsOfPlaces (arithFrobC q K N) W)
      (coeffSemilinearAut N τ) := by sorry
