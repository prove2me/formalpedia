-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_IsGluedSpecialization_exists_isGoodClass_apply_eq
-- name    : ModularCurve.PlaceSpecialization.IsGluedSpecialization.exists_isGoodClass_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/0b16beac-f717-5741-b2c8-96d7a433f27f
-- title:
--   Glued specialization is onto by good inertia-invariant classes
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, and an algebraically closed field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} : A \to k$. Fix further data $\mathrm{data}$ consisting of a monic polynomial $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, a hypothesis $hKr$ asserting the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$, and hypotheses $h\alpha$, $h\beta$ asserting that the two degeneracy ring homomorphisms $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ at level $N$ and prime $q$ over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialization `PlaceSpecialization` for these data, i.e. the package consisting of a map from the places of $\overline{\mathbb Q}(X_0(N))$ to the places of the field $\mathrm{modularFunctionFieldC}\,k\,N = k(\tilde j, \tilde j_N)$, a compatible homomorphism on degree-zero class groups, and the listed compatibilities of orders of vanishing of $j$ and $j_N$ under $\mathrm{red}$, and assume $q \nmid N$. Let $W$ be a finite set of places of $k(\tilde j, \tilde j_N)$ over $k$ whose members are exactly the places satisfying $\mathrm{IsSupersingularPlace}\ q\ N\ k$, and let $S = \mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\ q\ k\ N)\,W$ be the finite set of pairs obtained from $W$ by the node-pair embedding attached to the coefficientwise arithmetic $q$-Frobenius semilinear automorphism, i.e. the pairs $(w, \mathrm{Frob}\cdot w)$ for $w \in W$. Write $H = \mathrm{inertiaInvariants}\ A\ (Nq)$ for the subgroup of $\mathrm{JZero}(Nq) = \mathrm{Pic}^0(\overline{\mathbb Q}(X_0(Nq)))$ invariant under the inertia subgroup of $A$ over $\mathbb Q$, and let $G = \mathrm{GluedPic0}$ of $k(\tilde j, \tilde j_N)$ along $S$, the quotient of the admissible gluing data by the glued principal ones. Let $\mathrm{sp} : H \to G$ be an additive map which is a glued specialization for $P$ and $S$: whenever $D$ is a degree-zero divisor on $\overline{\mathbb Q}(X_0(Nq))$ whose class lies in $H$, $D$ satisfies $P.\mathrm{IsGoodDiv}$, and $x$ is an admissible gluing datum equal to $P.\mathrm{glueData}\ S\ D$, then $\mathrm{sp}$ of the class of $D$ is the class of $x$. Then for every $g \in G$ there is an $x \in H$ which is a good class, i.e. the class of some degree-zero divisor $D$ with $P.\mathrm{IsGoodDiv}\ D$ and $P.\mathrm{glueData}\ S\ D$ admissible, and which satisfies $\mathrm{sp}(x) = g$.
--
--   This is the surjectivity of specialization at a prime $q$ of semistable reduction, in the divisor and gluing-datum presentation: every degree-zero class on the two copies of $X_0(N)_k$ glued along the supersingular points and their Frobenius translates is hit by an inertia-invariant good class on $J_0(Nq)$. It is used in the constructions of torsion preimages through the component map and through the glued specialization map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_IsGluedSpecialization_exists_isGoodClass_apply_eq.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.IsGluedSpecialization.exists_isGoodClass_apply_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    {sp : ↥(inertiaInvariants A (N * q)) →+
      GluedPic0 k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W)}
    (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q k N) W) sp)
    (g : GluedPic0 k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W)) :
    ∃ x : ↥(inertiaInvariants A (N * q)),
      P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (x : JZero (N * q)) ∧ sp x = g := by sorry
