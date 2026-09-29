-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_IsGluedSpecialization_eq_zero_of_isGoodClass_of_nsmul_eq_zero_of_not_dvd_of_isModel
-- name    : ModularCurve.PlaceSpecialization.IsGluedSpecialization.eq_zero_of_isGoodClass_of_nsmul_eq_zero_of_not_dvd_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/500ab008-a574-596e-bd1d-a1875eb5e6ab
-- title:
--   Good kernel classes of order prime to q vanish
-- statement:
--   Fix a prime $q$ and a natural number $N \neq 0$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence $\Phi \bmod q = (Y^q - X)(Y - X^q)$, and hypotheses $h\alpha$, $h\beta$ that the two degeneracy embeddings of $\overline{\mathbb{Q}}$-modular function fields from level $N$ to level $Nq$ are integral. Let $P$ be a `PlaceSpecialization` for these data, let $q \nmid N$, and let $W$ be a finite set of places of the level-$N$ function field $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places (rational, affine-geometric, with $j$-value in the supersingular set for $q$). Let $R$ be a prolongation tuple for $P$ which is a model (the two divisor laws and the two cusp laws at $\infty$ and at $0$), satisfying the regularity law and the node-value law for $W$ and the fixed-point order law. Let $sp$ be an additive map from the inertia invariants of $J_0$ at level $Nq$, i.e. the classes in $\mathrm{Pic}^0$ of $\mathrm{modularFunctionFieldBar}(Nq)$ fixed by the inertia subgroup of $A$ over $\mathbb{Q}$, to the glued degree-zero class group over the node pairs $\{(w, \mathrm{arithFrobC}\,q\,k\,N \cdot w) : w \in W\}$, and assume $sp$ is a glued specialization for $P$: every degree-zero divisor $D$ whose support consists of places strictly on the first or strictly on the second side, and whose inertia-invariant class is represented by an admissible glued datum equal to $P$'s glue data of $D$, has $sp$ of its class equal to the class of that glued datum. Then for an inertia-invariant class $x$ which is good (represented by a degree-zero divisor $D$ with support strictly on one side or the other, whose glue data is admissible), with $sp(x) = 0$, and for $n$ with $n \neq 0$, $q \nmid n$ and $n \cdot x = 0$, one has $x = 0$.
--
--   This is the injectivity, on torsion of order prime to the residue characteristic, of the specialisation map from the inertia invariants of the Jacobian at level $Nq$ to the degree-zero class group of the glued two-component special fibre, in the form used to analyse the $q$-adic behaviour of $J_0(Nq)$ at a prime $q$ exactly dividing the level. It feeds the injectivity statement [`ModularCurve.PlaceSpecialization.gluedSpecialization_componentMap_injective_primeToTorsion_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.gluedSpecialization_componentMap_injective_primeToTorsion_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_IsGluedSpecialization_eq_zero_of_isGoodClass_of_nsmul_eq_zero_of_not_dvd_of_isModel.lean

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

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.IsGluedSpecialization.eq_zero_of_isGoodClass_of_nsmul_eq_zero_of_not_dvd_of_isModel
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
    (x : ↥(inertiaInvariants A (N * q)))
    (hgood : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (x : JZero (N * q)))
    (hx : sp x = 0)
    (n : ℕ) (hn : n ≠ 0) (hqn : ¬ q ∣ n) (hnx : n • x = 0) : x = 0 := by sorry
