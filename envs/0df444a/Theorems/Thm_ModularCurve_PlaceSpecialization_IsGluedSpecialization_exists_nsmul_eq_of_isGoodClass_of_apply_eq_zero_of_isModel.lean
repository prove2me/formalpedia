-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_IsGluedSpecialization_exists_nsmul_eq_of_isGoodClass_of_apply_eq_zero_of_isModel
-- name    : ModularCurve.PlaceSpecialization.IsGluedSpecialization.exists_nsmul_eq_of_isGoodClass_of_apply_eq_zero_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/932494b6-0ec2-59d4-9b8f-50820a3ec29b
-- title:
--   Good classes in the kernel of a glued specialization are m-divisible
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ together with the Kronecker congruence `hKr` stating that the reduction of its bivariate polynomial $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of the level-$N$ into the level-$Nq$ Laurent-series function field. Let $P$ be a `PlaceSpecialization` for these data, and assume $q \nmid N$. Let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, and write $S$ for `nodePairsOfPlaces (arithFrobC q k N) W`, the set of node pairs obtained from $W$ by the coefficientwise $q$-power Frobenius semilinear automorphism. Let $R$ be a prolongation tuple over $P$ satisfying the model property `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law at $W$, and the order law at the places fixed by the square of the geometric Frobenius. Let $sp$ be an additive homomorphism from the inertia invariants of $A$ in `JZero (N * q)`, the degree-zero class group of the level-$Nq$ curve over $\overline{\mathbb Q}$, to the glued degree-zero class group `GluedPic0 k (modularFunctionFieldC k N) S`, and assume `hsp`, that $sp$ is a glued specialization: for every degree-zero divisor $D$ whose class is inertia-invariant and all of whose support consists of places that are strictly first or strictly second for $P$, and every admissible gluing datum $x$ equal to the glued datum of $D$, the value of $sp$ on the class of $D$ is the glued class of $x$. Finally let $m$ be a nonzero natural number with $q \nmid m$, and let $z$ be an inertia-invariant class which is good (representable by a degree-zero divisor with support of the above kind whose glued datum is admissible) and satisfies $sp(z) = 0$. Then there is an inertia-invariant class $y$ which is likewise good, satisfies $sp(y) = 0$, and satisfies $m \cdot y = z$.
--
--   This is the divisibility half of the torsion-lifting package for the specialization map at $q$: the good classes killed by $sp$ behave like the kernel of reduction of the Néron model of $J_0(Nq)$ at $q$, which is uniquely divisible by integers prime to the residue characteristic. It is used by [`ModularCurve.PlaceSpecialization.exists_torsion_preimage_componentMap_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_torsion_preimage_componentMap_of_isModel) and [`ModularCurve.PlaceSpecialization.exists_torsion_preimage_gluedSpecialization_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_torsion_preimage_gluedSpecialization_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_IsGluedSpecialization_exists_nsmul_eq_of_isGoodClass_of_apply_eq_zero_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.IsGluedSpecialization.exists_nsmul_eq_of_isGoodClass_of_apply_eq_zero_of_isModel
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
    {sp : ↥(inertiaInvariants A (N * q)) →+
      GluedPic0 k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W)}
    (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q k N) W) sp)
    (m : ℕ) (hm : m ≠ 0) (hqm : ¬ q ∣ m)
    (z : ↥(inertiaInvariants A (N * q)))
    (hz : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (z : JZero (N * q)))
    (hz0 : sp z = 0) :
    ∃ y : ↥(inertiaInvariants A (N * q)),
      P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (y : JZero (N * q)) ∧ sp y = 0 ∧ m • y = z := by sorry
