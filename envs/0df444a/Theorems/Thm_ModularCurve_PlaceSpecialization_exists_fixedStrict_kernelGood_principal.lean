-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_fixedStrict_kernelGood_principal
-- name    : ModularCurve.PlaceSpecialization.exists_fixedStrict_kernelGood_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/aa4121f9-5db4-5fae-881d-919df430c617
-- title:
--   Inertia-stable divisors modulo fixed strict and glue-trivial divisors
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $k$ an algebraically closed field of characteristic $q$ and $red : A \to k$ a ring homomorphism; let `data` be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, and let $h\alpha$, $h\beta$ assert integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb Q}$. Let $P$ be a place specialisation of this data, $R$ a level-one prolongation pair over $P$ satisfying the model property `IsModel` (the two divisor laws and the two cusp laws) and the order law `OrderLawFixed` at Frobenius-fixed places, and let $W$ be a finite set of places of $k(\tilde\jmath)=$ `modularFunctionFieldC k 1` consisting exactly of the supersingular places `ssPlaces q 1 k`. Let $X$ be a degree-zero divisor on the level-$q$ modular function field over $\overline{\mathbb Q}$ such that the arithmetic Galois action of every $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$ fixes $X$, and such that each place $V$ in the support of $X$ satisfies `P.IsStrictFst V` (the geometric Frobenius on places carries the first reduction of $V$ to its second reduction, and its square moves the first reduction) or `P.IsStrictSnd V` (the mirror condition) or has first reduction in $W$. Then there are degree-zero divisors $D_1, D_2$ such that every place in the support of $D_1$ is fixed by the whole inertia action and is strict of the first or second kind; every place in the support of $D_2$ is strict of the first or second kind; the glue datum of $D_2$ relative to the node pairs attached to $W$ by the coefficient Frobenius `arithFrobC q k 1`, namely the pair of pushforwards of the strict-first and strict-second parts of $D_2$ along the two reduction maps together with the trivial unit component, is admissible and has trivial class in the glued degree-zero class group; and $X - D_1 - D_2$ is principal, i.e. the divisor of a non-zero function.
--
--   This is the moving step in the specialisation of degree-zero divisor classes on $X_0(q)$ to the two-component special fibre at $q$: modulo principal divisors, an inertia-stable degree-zero divisor with strict or supersingular support differs from a divisor whose glued specialisation vanishes by a degree-zero divisor supported at inertia-fixed strict places. It feeds the statement that inertia-invariant classes are represented by divisors with inertia-fixed admissible support, used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_fixedStrict_kernelGood_principal.lean

import Mathlib
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve ModularCurve.PlaceSpecialization
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_fixedStrict_kernelGood_principal
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) = X)
    (hXgood : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) :
    ∃ (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))),
      (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧ (P.IsStrictFst V ∨ P.IsStrictSnd V)) ∧
      P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∧
      (∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W),
        GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), hadm⟩ = 0) ∧
      ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - D₁ - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by sorry
