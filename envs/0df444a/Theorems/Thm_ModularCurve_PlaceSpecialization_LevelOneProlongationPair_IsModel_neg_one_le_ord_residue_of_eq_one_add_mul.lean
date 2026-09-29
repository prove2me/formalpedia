-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_neg_one_le_ord_residue_of_eq_one_add_mul
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.neg_one_le_ord_residue_of_eq_one_add_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/402836d4-a939-5a86-9b55-c76d4fecb52a
-- title:
--   A simple pole bound at a strict-type-one reduction
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the $q$-th modular pair of $j$-expansions) satisfying the Kronecker congruence `hKr`, that the reduction of $\Phi$ modulo $q$ is $(C(X)^q-X)(C(X)-X^q)$, together with integrality hypotheses $h\alpha,h\beta$ for the two Hecke maps $\bar\alpha,\bar\beta$ at level $1$ and prime $q$, a place specialisation $P$ for these data, and a level-one prolongation pair $R=(R_1,R_2)$ for $P$ with $R$ a model, i.e. satisfying the two divisor laws and the cusp laws at $\infty$ and at $0$. Let $Q\neq Q'$ be places of the geometric modular function field of level $1\cdot q$ over $\overline{\mathbb Q}$, both of strict type one for $P$ (the geometric-level Frobenius carries `P.redFst` to `P.redSnd`, and its square does not fix `P.redFst`), with $P.\mathrm{redFst}\,Q'=P.\mathrm{redFst}\,Q$. Let $n$ be a natural number whose image in $k$ is nonzero, and let $g$ be an element of that function field lying in the integers of $R_1$, with nonzero $R_1$-residue, such that $\operatorname{ord}_Q g=-n$, $\operatorname{ord}_{Q'}g=n$, and $\operatorname{ord}_W g=0$ for every strict-type-one place $W$ with $P.\mathrm{redFst}\,W=P.\mathrm{redFst}\,Q$ other than $Q$ and $Q'$. Suppose finally $g=1+e\,\varepsilon$ for some $e\in A$ (via the structure map from $\overline{\mathbb Q}$) and some $\varepsilon$ in the integers of $R_1$ with nonzero $R_1$-residue. Then the order of the element `R.residue₁ ⟨ε, hε₁⟩` of the level-one modular function field over $k$ at the place $P.\mathrm{redFst}\,Q$ is at least $-1$.
--
--   This is the local step — at most a simple pole at each base point — of the first-order expansion argument bounding the residue of the primitive part of a torsion relation, used in the study of reduction on prime-to-$q$ torsion for the two Gauss prolongations of $X_0(q)$ in characteristic $q$. It is invoked in the corresponding statement for prolongation tuples, [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_neg_one_le_ord_residue_of_eq_one_add_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.neg_one_le_ord_residue_of_eq_one_add_mul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hQ : P.IsStrictTypeOne Q) (hQ' : P.IsStrictTypeOne Q') (hQQ' : P.redFst Q' = P.redFst Q) (hne : Q' ≠ Q)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg₁ : g ∈ R.R₁.integers) (hg₁' : R.R₁.residue ⟨g, hg₁⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictTypeOne W → P.redFst W = P.redFst Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (1 * q))) (hε₁ : ε ∈ R.R₁.integers) (hε₁' : R.R₁.residue ⟨ε, hε₁⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.redFst Q).ord (R.residue₁ ⟨ε, hε₁⟩) := by sorry
