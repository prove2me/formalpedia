-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ
-- name    : ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/955655bf-fb79-5b78-96eb-5e50132b7c29
-- title:
--   Frobenius-equivariant dictionary over an elliptic centre j=0,1728
-- statement:
--   Let $q$ be a prime and $N$ a positive integer with $q \nmid N$, and let $K$ be an algebraically closed field of characteristic $q$. Let $a \in K$ satisfy $a = 0$ or $a = 1728$, and suppose $a$ lies in [`ModularCurve.ssJSet q K`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every Weierstrass curve $W$ over $K$ that is elliptic and has $j(W) = a$ has no nonzero point $P$ of its affine model with $q \cdot P = 0$. The assertion is the existence of a bijection $e$ between two sets: on one side, the places $w$ of the modular function field $\mathrm{modularFunctionFieldC}\ K\ N = K(j(q), j(q^N))$ inside the Laurent series field over $K$ — a place being a proper valuation subring containing $K$ and a principal ideal ring — that belong to [`ModularCurve.ssPlaces q N K`](def/ModularCurve_SupersingularNodePlaces.html#L113) (those satisfying `IsSupersingularPlace q N K`) and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen}\ K\ N) = a$, where $\mathrm{evalAt}$ is reduction to the residue field followed by a chosen inverse of $K \to$ residue field; on the other side, the $\Gamma_0(N)$-moduli points $x$ over $K$ (classes of pairs consisting of an elliptic Weierstrass curve and a point of order $N$) lying in [`ModularCurve.ssLocus q N K`](def/ModularCurve_SupersingularModuli.html#L20), i.e. supersingular for $q$, with $j(x) = a$. Moreover $e$ intertwines the two Frobenius actions in the following form: for all $w, w'$ in the source, if the semilinear automorphism [`ModularCurve.arithFrobC q K N`](def/ModularCurve_CoeffSemilinearAut.html#L128) (coefficientwise $q$-power Frobenius on Laurent series) carries $w$ to $w'$, then the moduli point underlying $e(w')$ equals the image of the moduli point underlying $e(w)$ under `ModuliPoint.map` of the $q$-power Frobenius ring homomorphism of $K$.
--
--   This is the fibre over an elliptic centre $a \in \{0, 1728\}$ of the Frobenius-equivariant dictionary between supersingular places of the level-$N$ modular function field in characteristic $q$ and supersingular $\Gamma_0(N)$-moduli points over $K$; the centres $j = 0, 1728$ are separated from the remaining supersingular $j$-invariants because of the extra automorphisms of the corresponding curves. It is used to assemble the dictionary over all supersingular $j$-invariants in [`ModularCurve.exists_equiv_ssPlaces_ssLocus_frobenius_equivariant_univ`](thm.html#ModularCurve.exists_equiv_ssPlaces_ssLocus_frobenius_equivariant_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ.lean

import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ModuliPointMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ
    (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K]
    (a : K) (ha : a = 0 ∨ a = 1728) (hss : a ∈ ModularCurve.ssJSet q K) :
    ∃ e : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K ∧ w.evalAt (ModularCurve.jGeomGen K N) = a} ≃
          {x : ModularCurve.ModuliPoint N K // x ∈ ModularCurve.ssLocus q N K ∧ ModularCurve.ModuliPoint.j x = a},
      ∀ (w w' : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K ∧ w.evalAt (ModularCurve.jGeomGen K N) = a}),
        ModularCurve.arithFrobC q K N • (w : Place K (ModularCurve.modularFunctionFieldC K N))
            = (w' : Place K (ModularCurve.modularFunctionFieldC K N)) →
          ((e w' : {x : ModularCurve.ModuliPoint N K //
              x ∈ ModularCurve.ssLocus q N K ∧ ModularCurve.ModuliPoint.j x = a}) : ModularCurve.ModuliPoint N K)
            = ModularCurve.ModuliPoint.map (frobenius K q)
                ((e w : {x : ModularCurve.ModuliPoint N K //
                    x ∈ ModularCurve.ssLocus q N K ∧ ModularCurve.ModuliPoint.j x = a}) : ModularCurve.ModuliPoint N K) := by sorry
