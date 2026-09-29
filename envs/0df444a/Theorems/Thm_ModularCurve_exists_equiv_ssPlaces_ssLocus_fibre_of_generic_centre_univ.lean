-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ
-- name    : ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/36866912-5a75-5cef-9417-a84c85218610
-- title:
--   Frobenius-equivariant bijection of supersingular places and moduli points
-- statement:
--   Let $q$ be a prime and $N$ a nonzero natural number with $q \nmid N$, and let $K$ be an algebraically closed field of characteristic $q$. Write $F =$ [`ModularCurve.modularFunctionFieldC K N`](def/ModularCurve_JqCoeff.html#L61) for the subfield of the Laurent series field $K((t))$ generated over $K$ by the $j$-series `jqModC K` and its $N$-fold expansion `jqNModC K N`, and let $j_{\mathrm{gen}} =$ [`ModularCurve.jGeomGen K N`](def/ModularCurve_CharLSpecialFibreLevelNDictionary.html#L82) be the element of $F$ given by `jqModC K`. A place of $F$ over $K$ is a valuation subring of $F$ containing $K$, distinct from $F$, whose ring is a principal ideal ring, and `Place.evalAt` sends $f \in F$ to the preimage in $K$ of the residue class of $f$ when $f$ lies in the valuation ring, and to $0$ otherwise. The assertion is the existence of a bijection $e$ from the set of places $w$ of $F$ lying in [`ModularCurve.ssPlaces q N K`](def/ModularCurve_SupersingularNodePlaces.html#L113) (those satisfying `IsSupersingularPlace q N K`) with $w(j_{\mathrm{gen}}) \neq 0$ and $\neq 1728$, onto the set of $\Gamma_0(N)$-moduli points $x$ over $K$ (classes of pairs consisting of an elliptic curve and a point of exact order $N$) lying in [`ModularCurve.ssLocus q N K`](def/ModularCurve_SupersingularModuli.html#L20), i.e. with `ModuliPoint.IsSupersingular q`, and with $j(x) \neq 0$ and $\neq 1728$, such that: first, $j(e(w)) = w(j_{\mathrm{gen}})$ for every such $w$; and second, whenever the translate of $w$ by the semilinear automorphism [`ModularCurve.arithFrobC q K N`](def/ModularCurve_CoeffSemilinearAut.html#L128) (the coefficientwise $q$-power Frobenius on Laurent series together with Frobenius on $K$) again lies in [`ModularCurve.ssPlaces q N K`](def/ModularCurve_SupersingularNodePlaces.html#L113) and has evaluation at $j_{\mathrm{gen}}$ different from $0$ and $1728$, the value of $e$ at that translate is the image of $e(w)$ under `ModuliPoint.map (frobenius K q)`, the base change of the moduli datum along the $q$-power Frobenius of $K$.
--
--   This is the dictionary identifying the supersingular points of the special fibre of the level-$N$ modular curve in characteristic $q$, described valuation-theoretically as places of the modular function field, with supersingular $\Gamma_0(N)$-moduli points over $K$, away from the elliptic points $j = 0, 1728$, and it records that the identification matches arithmetic Frobenius on places with Frobenius base change of moduli. It is used by [`ModularCurve.exists_equiv_ssPlaces_ssLocus_frobenius_equivariant_univ`](thm.html#ModularCurve.exists_equiv_ssPlaces_ssLocus_frobenius_equivariant_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.lean

import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ModuliPointMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ
    (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K] :
    ∃ e : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728} ≃
          {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728},
      (∀ w : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728},
        ModularCurve.ModuliPoint.j ((e w : {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)
          = (w : Place K (ModularCurve.modularFunctionFieldC K N)).evalAt
              (ModularCurve.jGeomGen K N)) ∧
      (∀ (w : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728})
        (hw' : ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))
               ∈ ModularCurve.ssPlaces q N K
              ∧ (ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))).evalAt
                    (ModularCurve.jGeomGen K N) ≠ 0
              ∧ (ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))).evalAt
                    (ModularCurve.jGeomGen K N) ≠ 1728),
        ((e ⟨_, hw'⟩ : {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)
          = ModularCurve.ModuliPoint.map (frobenius K q)
              ((e w : {x : ModularCurve.ModuliPoint N K //
                  x ∈ ModularCurve.ssLocus q N K
                    ∧ ModularCurve.ModuliPoint.j x ≠ 0
                    ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)) := by sorry
