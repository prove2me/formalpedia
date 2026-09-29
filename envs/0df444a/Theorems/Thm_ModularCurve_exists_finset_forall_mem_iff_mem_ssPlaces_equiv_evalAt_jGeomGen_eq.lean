-- Prove2me | Theorems.Thm_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
-- name    : ModularCurve.exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/eeaacae1-4231-50d3-9f1f-9de1431f69d8
-- title:
--   Supersingular places of the j-line versus supersingular j-invariants
-- statement:
--   Let $q$ be a prime and let $k$ be an algebraically closed field of characteristic $q$. Let $S$ be a finite subset of $k$ whose members are exactly the elements of `ssJSet q k`, that is, the $j \in k$ such that every elliptic Weierstrass curve $W$ over $k$ with $W.j = j$ has no nonzero point $P$ of its affine model with $q \cdot P = 0$. Work with the level-one modular function field `modularFunctionFieldC k 1`, the intermediate field of the Laurent series field $k((q))$ generated over $k$ by `jqModC k` and `jqNModC k 1`, and with its distinguished element `jGeomGen k 1`, namely `jqModC k` viewed inside that field; places of this field over $k$ are valuation subrings containing the image of $k$, different from the whole field, and principal ideal rings. The assertion is that there exist a finite set $W$ of such places and a bijection $\tau$ from $S$ onto $W$ with the following two properties: a place $w$ lies in $W$ if and only if $w$ lies in `ssPlaces q 1 k`, i.e. $w$ satisfies `IsRational`, satisfies `IsAffineGeomPlace k 1`, and its residue evaluation `evalAt` of `jGeomGen k 1` lies in `ssJSet q k`; and for every $a \in S$ the evaluation of `jGeomGen k 1` at the place $\tau(a)$ equals $a$.
--
--   This is the dictionary between the two indexings of the supersingular locus of the level-one special fibre in characteristic $q$: by supersingular $j$-invariants, and by the supersingular places of the rational function field of the $j$-line, each such place being the rational affine place centred at its $j$-value. It is used in the construction of prolongation tuples and specialisation data for places of modular curves, where the supersingular points must be enumerated as a finite index set matched with their $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SpecializeModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S : Finset k) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q k) :
    ∃ (W : Finset (Place k (modularFunctionFieldC k 1))) (τ : ↥S ≃ ↥W),
      (∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) ∧
        ∀ a : ↥S, (τ a : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1) = (a : k) := by sorry
