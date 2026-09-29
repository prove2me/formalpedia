-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/c48b75a8-0fc8-590d-8688-4024812519e8
-- title:
--   Simple pole bound for the second residue of ε
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive level $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix $data$ a monic bivariate modular polynomial datum for $q$ satisfying the Kronecker congruence $\Phi \equiv (X^q-Y)(X-Y^q)$, integrality hypotheses $h\alpha, h\beta$ for the two degeneracy maps at level $N$, $q$, a specialisation $P$ of places, and a prolongation tuple $R$ for $P$ satisfying the four model laws (the two divisor laws and the two cusp laws). Let $Q \ne Q'$ be places of the level-$Nq$ modular function field over $\overline{\mathbb Q}$, both strict of the second kind for $P$ (their first reduction is the Frobenius image of their second reduction, and the second reduction is not fixed by the square of Frobenius), with equal second reductions $P.\mathrm{reduceSnd}\,Q' = P.\mathrm{reduceSnd}\,Q$. Assume $q \nmid N$, that $P.\mathrm{reduceSnd}\,Q$ is an affine geometric place (both moduli generators $j$ and $j_N$ lie in its valuation subring), and that the value $a$ of $j$ there satisfies $a \ne 0$, $a \ne 1728$. Let $n$ be a natural number invertible in $k$, and let $g$ be $R_2$-integral with nonzero second residue, with $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$, and $\operatorname{ord}_W g = 0$ for every other strict second-kind place $W$ with the same second reduction. If $g = 1 + e\,\varepsilon$ for some $e \in A$ and some $R_2$-integral $\varepsilon$ with nonzero second residue, then the order of the reduction $R.\mathrm{residue}_2\,\varepsilon$ at the place $P.\mathrm{reduceSnd}\,Q$ is at least $-1$.
--
--   This is the second-kind counterpart of the bound saying that the primitive part $\varepsilon$ of a multiplicative $n$-torsion relation $g = 1 + e\varepsilon$ has at worst a simple pole on the level-$N$ special fibre, in the residue disc of a base point whose $j$-invariant avoids $0$ and $1728$. It feeds the computation of divisor-class relations [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hQ : P.IsStrictSnd Q) (hQ' : P.IsStrictSnd Q') (hQQ' : P.reduceSnd Q' = P.reduceSnd Q) (hne : Q' ≠ Q)
    (hQaff : IsAffineGeomPlace k N (P.reduceSnd Q))
    (hqN : ¬ q ∣ N)
    (a : k) (ha : (P.reduceSnd Q).evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (N * q))) (hg₂ : g ∈ R.R₂.integers) (hg₂' : R.R₂.residue ⟨g, hg₂⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictSnd W → P.reduceSnd W = P.reduceSnd Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (N * q))) (hε₂ : ε ∈ R.R₂.integers) (hε₂' : R.R₂.residue ⟨ε, hε₂⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.reduceSnd Q).ord (R.residue₂ ⟨ε, hε₂⟩) := by sorry
