-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor
-- name    : ModularCurve.PlaceSpecialization.depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/17a27bcd-d176-5ba2-9260-f6ef68ad3796
-- title:
--   Vanishing of the depth functional on good divisors
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ together with a proof `hKr` of the Kronecker congruence $\Phi \bmod q = (C(X)^q - X)(C(X) - X^q)$, and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps $\overline{\mathbb Q}$-base changed from level $1$ to level $q$. Let $P$ be a `PlaceSpecialization` record for these data at level $N = 1$, packaging a specialisation map on places together with a homomorphism on degree-zero divisor class groups and the compatibility conditions on $j$ recorded in that structure. Let $g$ be a semilinear automorphism of $k$-extension $\mathrm{modularFunctionFieldC}\ k\ 1 = k(j, j_1)$, let $W$ be a finite set of places of that field such that every $w \in W$ satisfies $\mathrm{frobOnPlacesGeomLevel}^2(w) = w$, where $\mathrm{frobOnPlacesGeomLevel}$ is the operation restricting a place along the $q$-power $q$-expansion embedding and transporting it back, let $e$ be an arbitrary $\mathbb N$-valued function on places, $\mathrm{depth}$ an arbitrary $\mathbb N$-valued function on places of $\mathrm{modularFunctionFieldBar}(1 \cdot q)$, and $s_0$ an element of the finite set $\mathrm{nodePairsOfPlaces}\ g\ W$, the image of $W$ under the injection $\mathrm{smulNodePairEmb}\ g$ into pairs of places. Finally let $D$ be a divisor on $\mathrm{modularFunctionFieldBar}(1 \cdot q)$ over $\overline{\mathbb Q}$ which is good for $P$, i.e. every place in the support of $D$ is of strict type one ($\mathrm{frob}(\mathrm{redFst}\,V) = \mathrm{redSnd}\,V$ and $\mathrm{frob}^2(\mathrm{redFst}\,V) \neq \mathrm{redFst}\,V$) or of strict type two ($\mathrm{redFst}\,V = \mathrm{frob}(\mathrm{redSnd}\,V)$ and $\mathrm{frob}^2(\mathrm{redSnd}\,V) \neq \mathrm{redSnd}\,V$). The conclusion is the identity, in the $\mathbb Z$-dual of the character lattice of $\mathrm{nodePairsOfPlaces}\ g\ W$, $$\mathrm{depthDual}_{g,W}(\mathrm{depth}, D) + \deg(\mathrm{sndDiv}\ D)\cdot\bigl(e(s_{0,1})\,\mathrm{crossingCoord}(s_0)\bigr) = (\mathrm{branchDegrees}\ D)_2 \cdot \bigl(e(s_{0,1})\,\mathrm{crossingCoord}(s_0)\bigr),$$ where $\mathrm{depthDual}$ is the sum over $s \in \mathrm{nodePairsOfPlaces}\ g\ W$ of the value at $s_1$ of the divisor $\sum_V D(V)\,\mathrm{depth}(V)\cdot[\mathrm{reduceFst}\,V]$ times the coordinate functional $\mathrm{crossingCoord}(s)$, $\mathrm{sndDiv}\ D$ is the part of $D$ supported on places $V$ with $\mathrm{reduceFst}\,V = \mathrm{frob}(\mathrm{reduceSnd}\,V)$ and $\mathrm{frob}^2(\mathrm{reduceSnd}\,V) \neq \mathrm{reduceSnd}\,V$, and $(\mathrm{branchDegrees}\ D)_2$ is the degree of the strict-type-two part of $D$.
--
--   This is the good-divisor clause of the component-specialisation law at level one: for a divisor all of whose points reduce to strict type one or two, the depth functional attached to the supersingular node pairs vanishes, so the component combination is governed by the strict-type-two branch degree alone, and the asserted identity holds for an arbitrary weight function $\mathrm{depth}$ and arbitrary width function $e$. It is used in the construction of prolongation tuples for a place specialisation, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_comp_depthCompLaw_and_surjective_levelOne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_comp_depthCompLaw_and_surjective_levelOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (g : SemilinearAut k (modularFunctionFieldC k 1))
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w ∈ W, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w)
    (e : Place k (modularFunctionFieldC k 1) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ)
    (s₀ : ↥(nodePairsOfPlaces g W))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hgood : P.IsGoodDivisor D) :
    P.depthDual g W depth D +
        Divisor.degree (P.sndDiv D) •
          ((((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ)) •
            crossingCoord s₀) =
      (P.branchDegrees D).2 •
        ((((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ)) •
          crossingCoord s₀) := by sorry
