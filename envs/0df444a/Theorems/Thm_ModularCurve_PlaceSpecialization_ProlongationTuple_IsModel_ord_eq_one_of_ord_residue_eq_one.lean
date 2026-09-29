-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_ord_eq_one_of_ord_residue_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.ord_eq_one_of_ord_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/bfd96120-5ad9-54a2-a9e2-56d5f1161656
-- title:
--   Function with uniformising residue is a parameter of the disc
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix furthermore `data`, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, together with a proof `hKr` that $\Phi$ reduces modulo $q$ to $(\mathrm{C}\,X^{q} - X)(\mathrm{C}\,X - X^{q})$, proofs `hα`, `hβ` that the two Hecke maps `heckeAlphaBar` and `heckeBetaBar` at level $N$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms, and a place specialisation $P$ for these data. Assume $q \nmid N$. Let $R$ be a prolongation tuple over $P$ which is a model, i.e. satisfies the two divisor laws `DivisorLawFst`, `DivisorLawSnd` and the two cusp laws `CuspLawInfty`, `CuspLawZero`. Let $Q$ be a place of the field `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$ (a proper valuation subring containing the base field whose ring is a principal ideal ring) which is strict of the first kind for $P$: the geometric-level Frobenius `frobOnPlacesGeomLevel` carries the first reduction `P.reduceFst Q` to the second reduction `P.reduceSnd Q`, and its square does not fix `P.reduceFst Q`. Let $t$ be an element of `modularFunctionFieldBar (N * q)` lying in `R.smoothLocalRingFst (P.reduceFst Q)`, the intersection of the ring of `R.R₁`-integers with the valuation rings of all places $W$ that are strict of the first kind for $P$ and satisfy `P.reduceFst W = P.reduceFst Q`; assume $\operatorname{ord}_Q(t) > 0$, that $t$ is an `R.R₁`-integer, and that the first residue `R.residue₁` of $t$, an element of the characteristic-$q$ modular function field `modularFunctionFieldC k N`, has order exactly $1$ at `P.reduceFst Q`. Then $\operatorname{ord}_Q(t) = 1$, and $\operatorname{ord}_W(t) = 0$ for every place $W \ne Q$ of `modularFunctionFieldBar (N * q)` that is strict of the first kind for $P$ and has the same first reduction as $Q$.
--
--   This is the disc-parameter statement for the residue disc of the first kind above a place of the reduction: a function integral on the disc whose residue is a uniformiser at the reduced place vanishes simply at one point of the disc and nowhere else in it. It is obtained from the one-sided form of the first divisor law `divisorLawFst_oneSided` of a model tuple, which equates the sum of the orders of $t$ over the disc with the order of its residue, all terms being non-negative; it is used to show that quotients by such a function again lie in the local ring of the disc, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.div_mem_smoothLocalRingFst_of_ord_residue_eq_one`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.div_mem_smoothLocalRingFst_of_ord_residue_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_ord_eq_one_of_ord_residue_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.ord_eq_one_of_ord_residue_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hQ : P.IsStrictFst Q)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht : t ∈ R.smoothLocalRingFst (P.reduceFst Q)) (htQ : 0 < Q.ord t)
    (ht₁ : t ∈ R.R₁.integers) (htv : (P.reduceFst Q).ord (R.residue₁ ⟨t, ht₁⟩) = 1) :
    Q.ord t = 1 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.IsStrictFst W → P.reduceFst W = P.reduceFst Q → W ≠ Q → W.ord t = 0 := by sorry
