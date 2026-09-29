-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_jumpLaw_of_isModel_of_oneSidedRegularityLaw
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.jumpLaw_of_isModel_of_oneSidedRegularityLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/38a814d7-087e-5e3c-a7d3-9c753429f29f
-- title:
--   Gauss jump law from model and one-sided regularity
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $N\ge 1$, and $k$ an algebraically closed field of characteristic $q$ with a ring homomorphism $\mathrm{red}\colon A\to k$; let $data$ consist of a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$, let $hKr$ assert that its reduction mod $q$ factors as $(X^q-Y)(X-Y^q)$ in the bivariate form used here, and let $h\alpha$, $h\beta$ assert integrality of the two Hecke ring homomorphisms $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and $q$. Assume $q\nmid N$, let $P$ be a place specialisation for these data, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\,q\,N\,k$, and let $R$ be a prolongation tuple over $P$ (a reduction $\overline{\mathrm{red}}$ on the residue field of $A$, a comparison embedding $\iota$, and two regular prolongations $R_1,R_2$ of the level-$Nq$ function field related by the Atkin–Lehner involution). Suppose $R$ is a model, i.e. satisfies both divisor laws and both cusp laws, and satisfies the one-sided regularity law relative to $W$. Then $R$ satisfies the Gauss jump law: for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, every $f$ integral for both $R_1$ and $R_2$, and all divisors $D,E$ on the level-$Nq$ curve with $D$ supported on places that are strict of the first or second kind for $P$ and with $D+(\sigma\cdot E-E)=\operatorname{div} f$ pointwise, vanishing of the $R_2$-residue of $f$ together with non-vanishing of its $R_1$-residue forces the degree of the strict-second-kind part of $D$ to be positive, and symmetrically with the two sides exchanged.
--
--   This is the jump relation at the supersingular points of the special fibre at $q$ of the curve of level $Nq$: a function regular and non-vanishing on exactly one of the two components must acquire positive degree of zeros along the other component. It is used by [`ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel) in the analysis of the component group and the Eichler–Shimura relation underlying level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_jumpLaw_of_isModel_of_oneSidedRegularityLaw.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTuple_JumpLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.jumpLaw_of_isModel_of_oneSidedRegularityLaw
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (hOS : R.OneSidedRegularityLaw W) :
    GaussJump.JumpLaw R := by sorry
