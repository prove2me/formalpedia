-- Prove2me | Theorems.Thm_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ
-- name    : ModularCurve.exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/94ca4661-f6c2-5c56-b91e-aaaf0fb1878a
-- title:
--   Cyclic N-subgroups parametrise places and moduli points over j(E₀)
-- statement:
--   Let $q$ be a prime and $N$ a positive integer with $q \nmid N$, let $K$ be an algebraically closed field of characteristic $q$ with decidable equality, and let $E_0$ be an elliptic Weierstrass curve over $K$ whose coefficients are fixed by the $q$-power Frobenius, i.e. `E₀.map (frobenius K q) = E₀`. Write $S$ for the type of additively cyclic subgroups $H$ of the affine points of $E_0$ having exactly $N$ elements. The assertion is that there are maps $f$ from $S$ to the places of [`ModularCurve.modularFunctionFieldC K N`](def/ModularCurve_JqCoeff.html#L61) over $K$ (valuation subrings of the Laurent series field that contain the image of $K$, are not everything, and are principal ideal rings; the field itself is generated over $K$ by the $q$-expansions `jqModC K` and `jqNModC K N`) and $g$ from $S$ to [`ModularCurve.ModuliPoint N K`](def/ModularCurve_ModuliPoint.html#L35) (the quotient of the pairs consisting of an elliptic curve over $K$ together with a point of additive order $N$, by the step relation) such that: each $f H$ has positive order at $u :=$ `jGeomGen K N` $- j(E_0)$, where the order is $-\log$ of the associated adic valuation; every place with positive order at $u$ is some $f H$; $f H = f H'$ holds exactly when some variable change $\gamma$ over $K$ with $\gamma \bullet E_0 = E_0$ carries every $T \in H$, via the induced map `vcInvFun` on points, to a member of $H'$ (heterogeneously, the target being the points of $\gamma \bullet E_0$); $g H = g H'$ holds exactly when $f H = f H'$; every $g H$ has $j$-invariant $j(E_0)$, and every moduli point of $j$-invariant $j(E_0)$ is some $g H$; and for every $H$ there is $H'$ with $f H'$ the image of $f H$ under the semilinear automorphism `arithFrobC q K N` (coefficientwise $q$-power Frobenius on Laurent series, acting on places) and $g H'$ the image of $g H$ under `ModuliPoint.map (frobenius K q)`.
--
--   This is the dictionary between the fibre of the level-$N$ modular curve over a $j$-invariant in characteristic $q$ prime to $N$ and the cyclic subgroups of order $N$ of the corresponding elliptic curve, in the form of two parametrisations compatible with each other, with the variable-change action, and with arithmetic Frobenius. It is used in the analysis of the supersingular places of the special fibre, via [`ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ`](thm.html#ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.lean

import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_ModuliPointMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K]
    [DecidableEq K] [CharP K q] [IsAlgClosed K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (hfr : E₀.map (frobenius K q) = E₀) :
    ∃ (f : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
          AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldC K N))
      (g : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
          ModularCurve.ModuliPoint N K),
      (∀ H, 0 < (f H).ord (ModularCurve.jGeomGen K N -
          algebraMap K (ModularCurve.modularFunctionFieldC K N) E₀.j)) ∧
      (∀ w : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldC K N),
        0 < w.ord (ModularCurve.jGeomGen K N -
          algebraMap K (ModularCurve.modularFunctionFieldC K N) E₀.j) → ∃ H, f H = w) ∧
      (∀ H H', f H = f H' ↔ ∃ γ : WeierstrassCurve.VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1,
          HEq (WeierstrassCurve.Affine.Point.vcInvFun γ E₀.toAffine T) T') ∧
      (∀ H H', g H = g H' ↔ f H = f H') ∧
      (∀ H, ModularCurve.ModuliPoint.j (g H) = E₀.j) ∧
      (∀ x : ModularCurve.ModuliPoint N K, ModularCurve.ModuliPoint.j x = E₀.j → ∃ H, g H = x) ∧
      (∀ H, ∃ H', f H' = ModularCurve.arithFrobC q K N • f H ∧
        g H' = ModularCurve.ModuliPoint.map (frobenius K q) (g H)) := by sorry
