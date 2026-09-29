-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq
-- name    : ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/beefe992-ab50-50e7-8415-c6e4f300449e
-- title:
--   Inertia-fixed strict points of both types with distinct reductions
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $k$ an algebraically closed field of characteristic $q$ and $red : A \to k$ a ring homomorphism. Let `data` be a `ModularPolynomialData` for $q$ (a monic $\Phi$ in $(\mathbb Z[X])[X]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions $j$, $j_q$), let `hKr` assert the Kronecker congruence that $\Phi$ reduces modulo $q$ to $(\mathrm C(X)^q - X)\,(\mathrm C(X) - X^q)$, and let `hα`, `hβ` assert integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the base-changed level-one modular function field over $\overline{\mathbb Q}$ into the level-$1\cdot q$ one. Let $P$ be a `PlaceSpecialization A q 1 data hKr k red hα hβ`: a specialisation map `P.sp` on places together with a homomorphism on degree-zero divisor classes, subject to the compatibility conditions relating the orders of the $j$- and $j_N$-expansions to those of their reductions along `red`. For a place $W$ of `modularFunctionFieldBar (1 * q)`, $P.\mathrm{redFst}(W)$ is obtained by restricting $W$ along `heckeAlphaBar` and applying `P.sp`, and $P.\mathrm{redSnd}(W)$ likewise along `heckeBetaBar`; both are places of `modularFunctionFieldC k 1`. Then for every finite set $B$ of places of `modularFunctionFieldC k 1` and all $m_1, m_2 \in \mathbb N$ there are families $Q_1 : \mathrm{Fin}\,m_1 \to$ places of `modularFunctionFieldBar (1 * q)` and $Q_2 : \mathrm{Fin}\,m_2 \to$ places of the same field such that: each $Q_1(i)$ is of strict type one, i.e. the geometric-level Frobenius `frobOnPlacesGeomLevel k 1 data hKr` carries $P.\mathrm{redFst}(Q_1(i))$ to $P.\mathrm{redSnd}(Q_1(i))$ while its square does not fix $P.\mathrm{redFst}(Q_1(i))$; each $Q_2(j)$ is of strict type two, i.e. $P.\mathrm{redFst}(Q_2(j))$ is the Frobenius image of $P.\mathrm{redSnd}(Q_2(j))$ while the square of Frobenius does not fix $P.\mathrm{redSnd}(Q_2(j))$; the maps $i \mapsto P.\mathrm{redFst}(Q_1(i))$ and $j \mapsto P.\mathrm{redSnd}(Q_2(j))$ are injective; none of these reductions lies in $B$; and every $Q_1(i)$ and every $Q_2(j)$ is fixed by the action of `arithmeticGalois (modularFunctionFieldFull (1 * q)) σ` for each $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ` of $A$, that is, by coefficientwise application of $\sigma$ to Laurent series.
--
--   This is the level-one supply of arbitrarily many unramified points of $X_0(q)$ over $\overline{\mathbb Q}$, of each of the two strict types, whose specialisations are pairwise distinct, avoid a prescribed finite set of places of the characteristic-$q$ $j$-line, and which are fixed by the inertia group of $A$; classically it comes from Hensel lifting of smooth points on the two components of the special fibre of the Deligne–Rapoport model. It is used to produce inertia-stable auxiliary pole divisors in the construction of equivariant point-moving functions and in the annulus-datum and divisor-class arguments at level $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (B : Finset (Place k ↥(modularFunctionFieldC k 1))) (m₁ m₂ : ℕ) :
    ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      (∀ i, P.IsStrictTypeOne (Q₁ i)) ∧ (∀ j, P.IsStrictTypeTwo (Q₂ j)) ∧
      (Function.Injective fun i => P.redFst (Q₁ i)) ∧
      (Function.Injective fun j => P.redSnd (Q₂ j)) ∧
      (∀ i, P.redFst (Q₁ i) ∉ B) ∧ (∀ j, P.redSnd (Q₂ j) ∉ B) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂ j = Q₂ j) := by sorry
