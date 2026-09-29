-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_ssPlaces_ssLocus_frobenius_equivariant_univ
-- name    : ModularCurve.exists_equiv_ssPlaces_ssLocus_frobenius_equivariant_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/15f15ca0-a4b8-5bd7-80fe-5d6a042dc469
-- title:
--   Frobenius-equivariant bijection: supersingular places and supersingular moduli points
-- statement:
--   Fix natural numbers $q$ and $N$ with $N \neq 0$ and $q \nmid N$, and let $K$ be a field with decidable equality, with $q$ prime, of characteristic $q$, and algebraically closed. Write $F =$ [`ModularCurve.modularFunctionFieldC K N`](def/ModularCurve_JqCoeff.html#L61) for the subfield of the Laurent series field $K((q))$ generated over $K$ by the series `jqModC K` and its $N$-fold expansion `jqNModC K N`. A place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring; [`ModularCurve.ssPlaces q N K`](def/ModularCurve_SupersingularNodePlaces.html#L113) is the set of such places satisfying the predicate `IsSupersingularPlace q N K`, and [`ModularCurve.ssLocus q N K`](def/ModularCurve_SupersingularModuli.html#L20) is the set of $\Gamma_0(N)$-moduli points over $K$ satisfying `IsSupersingular q`. The assertion is that there is a bijection $e$ from `ssPlaces q N K` onto `ssLocus q N K` such that: (i) for every supersingular place $w$, the $j$-invariant of the moduli point $e(w)$ equals the residue evaluation of `jGeomGen K N` at $w$, the value being $0$ when that element is not in the valuation subring; and (ii) whenever the translate of $w$ under the semilinear automorphism `arithFrobC q K N` (coefficientwise $q$-power Frobenius on Laurent series, paired with Frobenius on $K$) again lies in `ssPlaces q N K`, the moduli point attached by $e$ to that translate is the image of $e(w)$ under transport of moduli points along the Frobenius endomorphism `frobenius K q` of $K$.
--
--   This is the dictionary identifying the supersingular points of the characteristic-$q$ fibre of the level-$N$ modular curve, described through $\Gamma_0(N)$-moduli of elliptic curves, with the supersingular places of the modular function field, compatibly with $j$ and with the arithmetic Frobenius. It is assembled from the corresponding statements over the fibres $j = 0$, $j = 1728$ and generic $j$, and is used to show that the square of the Frobenius action on places fixes every supersingular place over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_ssPlaces_ssLocus_frobenius_equivariant_univ.lean

import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ModuliPointMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.exists_equiv_ssPlaces_ssLocus_frobenius_equivariant_univ
    (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K] :
    ∃ e : ↥(ModularCurve.ssPlaces q N K) ≃ ↥(ModularCurve.ssLocus q N K),
      (∀ w : ↥(ModularCurve.ssPlaces q N K),
        ModularCurve.ModuliPoint.j (e w : ModularCurve.ModuliPoint N K)
          = (w : Place K (ModularCurve.modularFunctionFieldC K N)).evalAt
              (ModularCurve.jGeomGen K N)) ∧
      (∀ (w : ↥(ModularCurve.ssPlaces q N K))
        (hw' : ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))
               ∈ ModularCurve.ssPlaces q N K),
        ((e ⟨_, hw'⟩ : ↥(ModularCurve.ssLocus q N K)) : ModularCurve.ModuliPoint N K)
          = ModularCurve.ModuliPoint.map (frobenius K q)
              (e w : ModularCurve.ModuliPoint N K)) := by sorry
