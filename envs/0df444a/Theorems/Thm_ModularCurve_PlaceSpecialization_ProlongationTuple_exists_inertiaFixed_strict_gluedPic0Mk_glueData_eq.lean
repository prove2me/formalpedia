-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_strict_gluedPic0Mk_glueData_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_strict_gluedPic0Mk_glueData_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/85847022-11d0-57b5-a89f-2079b8b3bda5
-- title:
--   Surjectivity of the glued class map onto GluedPic⁰
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive level $N$, an algebraically closed field $k$ of characteristic $q$ and a ring map $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ together with the Kronecker congruence `hKr`, asserting that the reduction of $\Phi$ modulo $q$ equals $(C X^{q} - X)(C X - X^{q})$, and hypotheses $h\alpha$, $h\beta$ that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` from level $N$ into level $Nq$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialisation of this data, let $q \nmid N$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places `ssPlaces q N k` (rational, affine geometric, with $j$-value in the supersingular set), and let $S =$ `nodePairsOfPlaces (arithFrobC q k N) W` be the set of pairs $(w, \mathrm{Frob}\,w)$ for $w \in W$. Let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`. Then for every class $g$ in $\mathrm{GluedPic}^0$ for $S$ — the admissible gluing data modulo the glued principal ones — there is a degree-zero divisor $Dt$ on $\mathrm{modularFunctionFieldBar}\,(Nq)$ over $\overline{\mathbb{Q}}$ such that every place in the support of $Dt$ is fixed by $\mathrm{arithmeticGalois}(\mathrm{modularFunctionFieldFull}\,(Nq))\,\sigma$ for all $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, such that $Dt$ is good for $P$, meaning each place of its support is strict of the first kind or of the second kind, and such that the gluing datum $P.\mathrm{glueData}\,S\,Dt$ — the first and second strict parts of $Dt$ pushed forward along the two reductions, with vanishing node-unit component — is admissible and represents $g$.
--
--   This is the surjectivity statement for the map from inertia-fixed good degree-zero divisors at level $Nq$ to the glued degree-zero class group of the two copies of the level-$N$ fibre glued along the supersingular points, which models the Picard group of the semi-stable fibre of $X_0(Nq)$ at $q$. It is used in the construction of annulus data at level $N$, through [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_strict_gluedPic0Mk_glueData_eq.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_strict_gluedPic0Mk_glueData_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (g : GluedPic0 k ↥(modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W)) :
    ∃ Dt : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support,
          arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
      P.IsGoodDiv (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧
      ∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
            (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈
          GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W),
        GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W)
          ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
            (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadm⟩ = g := by sorry
