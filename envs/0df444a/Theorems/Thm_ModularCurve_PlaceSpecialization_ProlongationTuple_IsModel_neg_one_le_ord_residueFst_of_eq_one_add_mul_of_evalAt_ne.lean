-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f812e643-a2f0-58e2-8ad3-c4a5a223a9ba
-- title:
--   At most a simple pole for ε at affine base points
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the reduction mod $q$ of $\Phi$ is $(C X^q - X)(C X - X^q)$), integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke maps at level $N$ and $q$, a specialisation datum $P$ of places of $\overline{\mathbb Q}$-modular functions of level $N$, and a prolongation tuple $R$ for $P$ satisfying `IsModel`, i.e. the two divisor laws and the cusp laws at $\infty$ and at $0$. Assume $q \nmid N$. Let $Q \ne Q'$ be two places of the level-$Nq$ geometric function field $\overline{\mathbb Q}$-modular field which are strict of the first kind for $P$ (Frobenius carries `P.reduceFst` to `P.reduceSnd`, and the double Frobenius of `P.reduceFst` differs from it) and have the same first reduction, `P.reduceFst Q' = P.reduceFst Q`. Assume that first reduction $\bar v :=$ `P.reduceFst Q` is an affine geometric place, i.e. both $j$ and $j_N$ generators lie in its valuation subring, and that $a := \bar v(j)$, the evaluation of `jGeomGen k N` at $\bar v$, is neither $0$ nor $1728$. Let $n$ be a natural number whose image in $k$ is nonzero. Let $g$ be an element of the level-$Nq$ field lying in the integers of $R.R_1$, with nonzero $R_1$-residue, such that $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$, and $\operatorname{ord}_W g = 0$ for every place $W$ strict of the first kind with `P.reduceFst W = P.reduceFst Q` other than $Q$ and $Q'$. Suppose finally that $g = 1 + e\,\varepsilon$ for some $e \in A$ (via the structure map $\overline{\mathbb Q} \to$ the level-$Nq$ field) and some $\varepsilon$ in the integers of $R.R_1$ with nonzero $R_1$-residue. Then the order at $\bar v$ of the reduction `R.residue₁ ⟨ε, hε₁⟩` of $\varepsilon$, an element of the geometric level-$N$ function field over $k$, is at least $-1$.
--
--   This is the level-$N$ form, with explicit coordinate hypotheses, of the statement that the primitive part $\varepsilon$ of a relation $g = 1 + e\varepsilon$ coming from an $n$-torsion divisor relation acquires at most a simple pole on the special fibre at a base point of the first kind lying over a $j$-invariant different from $0$ and $1728$, where $j - j(Q)$ is a parameter of the residue disc. It is used for the corresponding bound for the second prolongation and in the computation of the divisor-theoretic identity for such torsion relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hQ : P.IsStrictFst Q) (hQ' : P.IsStrictFst Q') (hQQ' : P.reduceFst Q' = P.reduceFst Q) (hne : Q' ≠ Q)
    (hQaff : IsAffineGeomPlace k N (P.reduceFst Q))
    (hqN : ¬ q ∣ N)
    (a : k) (ha : (P.reduceFst Q).evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (N * q))) (hg₁ : g ∈ R.R₁.integers) (hg₁' : R.R₁.residue ⟨g, hg₁⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictFst W → P.reduceFst W = P.reduceFst Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (N * q))) (hε₁ : ε ∈ R.R₁.integers) (hε₁' : R.R₁.residue ⟨ε, hε₁⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.reduceFst Q).ord (R.residue₁ ⟨ε, hε₁⟩) := by sorry
