-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_ringHom_tExpansion_of_ord_residue_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_ringHom_tExpansion_of_ord_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/7abbfcec-19d7-5a8a-80ad-a34f95efc0e7
-- title:
--   Expansion homomorphism at a uniformiser of the residue disc
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $j$-expansions) satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke maps at level $N$ and $q$, and a place specialisation $P$ of these data. Assume $q \nmid N$, let $R$ be a prolongation tuple for $P$ satisfying the four model laws (the two divisor laws and the two cusp laws), and let $Q$ be a place of $\overline{\mathbb Q}$-modular function field of level $Nq$ which is strict of the first kind for $P$, i.e. Frobenius on places at geometric level $N$ carries $P.\mathrm{reduceFst}\,Q$ to $P.\mathrm{reduceSnd}\,Q$ while its square does not fix $P.\mathrm{reduceFst}\,Q$. Write $\mathcal O = R.\mathrm{smoothLocalRingFst}(P.\mathrm{reduceFst}\,Q)$ for the subring of $R_1$-integral functions lying in the valuation ring of every place $W$ that is strict of the first kind with $P.\mathrm{reduceFst}\,W = P.\mathrm{reduceFst}\,Q$. Let $t \in \mathcal O$ also lie in $R.R_1.\mathrm{integers}$, with first residue of valuation exactly $1$ at $P.\mathrm{reduceFst}\,Q$. Then there is a ring homomorphism $\varphi \colon \mathcal O \to A[[X]]$ such that: for all $r \in \mathcal O$ and all $m \in \mathbb N$ the quotient $\bigl(r - \sum_{i<m} \varphi(r)_i\, t^i\bigr)/t^m$ again lies in $\mathcal O$, the coefficients being transported from $A \subseteq \overline{\mathbb Q}$ into the function field; $\varphi(t) = X$; and $\varphi$ sends the image of any $c \in A$ (whenever that image lies in $\mathcal O$) to the constant series $C\,c$.
--
--   This packages the $t$-adic expansion of functions in the local ring of the residue disc of the first kind as a single ring homomorphism into $A[[X]]$, normalised so that $t \mapsto X$ and constants from $A$ go to constants; multiplicativity and additivity are exactly what allow identities in the function field to be pushed into the power series ring. It is used in the local step of the rigidity argument, namely by [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_ringHom_tExpansion_of_ord_residue_eq_one.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_ringHom_tExpansion_of_ord_residue_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hQ : P.IsStrictFst Q)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht : t ∈ R.smoothLocalRingFst (P.reduceFst Q))
    (ht₁ : t ∈ R.R₁.integers) (htv : (P.reduceFst Q).ord (R.residue₁ ⟨t, ht₁⟩) = 1) :
    ∃ φ : ↥(R.smoothLocalRingFst (P.reduceFst Q)) →+* PowerSeries ↥A,
      (∀ (r : ↥(R.smoothLocalRingFst (P.reduceFst Q))) (m : ℕ),
        ((r : ↥(modularFunctionFieldBar (N * q))) - ∑ i ∈ Finset.range m,
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((PowerSeries.coeff (R := ↥A) i (φ r) : A) : AlgebraicClosure ℚ) * t ^ i) / t ^ m ∈
        R.smoothLocalRingFst (P.reduceFst Q)) ∧
      φ ⟨t, ht⟩ = PowerSeries.X ∧
      (∀ (c : A) (hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ R.smoothLocalRingFst (P.reduceFst Q)),
          φ ⟨_, hc⟩ = PowerSeries.C (R := ↥A) c) := by sorry
