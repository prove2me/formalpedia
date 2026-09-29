-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_div_mem_smoothLocalRingFst_of_ord_residue_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.div_mem_smoothLocalRingFst_of_ord_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/0baf565f-c4f4-56c3-b0b2-d6a762ee49ad
-- title:
--   Division by a disc parameter at a strict place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix data $(\Phi,\dots)$ of type `ModularPolynomialData q` satisfying the Kronecker congruence $\Phi \bmod q = (C(X)^q - X)(C(X) - X^q)$, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps at level $N$ and $q$, and a place specialisation $P$ for these data. Assume $q \nmid N$, let $R$ be a prolongation tuple over $P$ satisfying the four model laws (the two divisor laws and the two cusp laws, i.e. `R.IsModel`), and let $Q$ be a place of $\overline{\mathbb Q}$-the modular function field $\mathrm{modularFunctionFieldBar}(Nq)$ which is strict of the first kind: Frobenius on places at geometric level $N$ carries $P.\mathrm{reduceFst}\,Q$ to $P.\mathrm{reduceSnd}\,Q$ and its square does not fix $P.\mathrm{reduceFst}\,Q$. Write $\mathcal O$ for `R.smoothLocalRingFst (P.reduceFst Q)`, the subring of functions lying in $R.R_1$'s ring of integers and in the valuation subring of every strict place of the first kind whose first reduction is $P.\mathrm{reduceFst}\,Q$. Let $t \in \mathcal O$ with $\mathrm{ord}_Q(t) > 0$, $t$ in $R.R_1$'s integers and $\mathrm{ord}_{P.\mathrm{reduceFst}\,Q}$ of its first residue equal to $1$, and let $r \in \mathcal O$ with $\mathrm{ord}_Q(r) > 0$. Then $r/t \in \mathcal O$.
--
--   This is the division step for a parameter $t$ on the residue disc of the first kind above $P.\mathrm{reduceFst}\,Q$: a function of $\mathcal O$ vanishing at $Q$ may be divided by $t$ without leaving $\mathcal O$, once the first residue of $t$ is a uniformiser at the reduced place. It serves as the inductive step in the construction of $t$-adic expansions of elements of $\mathcal O$, and is cited by [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_tExpansion_of_ord_residue_eq_one`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_tExpansion_of_ord_residue_eq_one); the order computations it rests on come from [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.ord_eq_one_of_ord_residue_eq_one`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.ord_eq_one_of_ord_residue_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_div_mem_smoothLocalRingFst_of_ord_residue_eq_one.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.div_mem_smoothLocalRingFst_of_ord_residue_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hQ : P.IsStrictFst Q)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht : t ∈ R.smoothLocalRingFst (P.reduceFst Q)) (htQ : 0 < Q.ord t)
    (ht₁ : t ∈ R.R₁.integers) (htv : (P.reduceFst Q).ord (R.residue₁ ⟨t, ht₁⟩) = 1)
    (r : ↥(modularFunctionFieldBar (N * q))) (hr : r ∈ R.smoothLocalRingFst (P.reduceFst Q)) (hrQ : 0 < Q.ord r) :
    r / t ∈ R.smoothLocalRingFst (P.reduceFst Q) := by sorry
