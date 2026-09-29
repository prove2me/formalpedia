-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/c6305500-cae4-5d86-a272-4a5e0997b568
-- title:
--   At most a simple pole at a second-kind place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ satisfying the Kronecker congruence, and integrality of the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $1$ and prime $q$, so that a place specialisation $P$ and a prolongation tuple $R$ for $P$ are available; assume $R$ satisfies `IsModel`, i.e. the two divisor laws and the cusp laws at $\infty$ and at $0$. Let $Q, Q'$ be places of $\overline{\mathbb{Q}}$ in the geometric modular function field of level $1\cdot q$ which are strict of the second kind for $P$ (so $P.\mathrm{reduceFst}$ of each is the Frobenius image of its $P.\mathrm{reduceSnd}$, and the double Frobenius image of the latter differs from it), with $P.\mathrm{reduceSnd}\,Q' = P.\mathrm{reduceSnd}\,Q$ and $Q' \neq Q$; assume the common reduction $P.\mathrm{reduceSnd}\,Q$ is affine, i.e. both $j$ and $j_N$ in their geometric level-$1$ incarnations lie in its valuation subring, and that its evaluation at $j$ equals $a \in k$ with $a \neq 0$ and $a \neq 1728$. Let $n$ be a natural number whose image in $k$ is nonzero. Let $g$ be an element of the function field lying in the integers of $R.R_2$, with nonzero $R_2$-residue, with $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for every place $W$ strict of the second kind with the same $P.\mathrm{reduceSnd}$ as $Q$ and distinct from $Q$ and $Q'$. Finally let $e \in A$ and let $\varepsilon$ lie in the integers of $R.R_2$ with nonzero $R_2$-residue, and suppose $g = 1 + e\,\varepsilon$ (the image of $e$ taken under the structure map). The conclusion is $-1 \leq \operatorname{ord}_{P.\mathrm{reduceSnd}\,Q}\big(R.\mathrm{residue}_2\,\varepsilon\big)$: the second prolongation residue of $\varepsilon$ has at most a simple pole at the reduced place.
--
--   This is the level-one case ($N = 1$, so level $q$ and the curve $X_0(q)$ with its two cusps) of the pole bound for the primitive part of an $n$-torsion relation at a base point of the second kind, away from $j = 0, 1728$. It feeds the summation identity [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hQ : P.IsStrictSnd Q) (hQ' : P.IsStrictSnd Q') (hQQ' : P.reduceSnd Q' = P.reduceSnd Q) (hne : Q' ≠ Q)
    (hQaff : IsAffineGeomPlace k 1 (P.reduceSnd Q))
    (a : k) (ha : (P.reduceSnd Q).evalAt (jGeomGen k 1) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg₂ : g ∈ R.R₂.integers) (hg₂' : R.R₂.residue ⟨g, hg₂⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictSnd W → P.reduceSnd W = P.reduceSnd Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (1 * q))) (hε₂ : ε ∈ R.R₂.integers) (hε₂' : R.R₂.residue ⟨ε, hε₂⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.reduceSnd Q).ord (R.residue₂ ⟨ε, hε₂⟩) := by sorry
