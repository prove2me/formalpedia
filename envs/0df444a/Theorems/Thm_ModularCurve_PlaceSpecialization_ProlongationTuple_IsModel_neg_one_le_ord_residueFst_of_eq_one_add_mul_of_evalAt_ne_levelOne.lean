-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/7e2366ec-5cb7-5aaa-b0cd-ca309ec43ba6
-- title:
--   A simple pole bound for the primitive part (level one)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, a datum `data` consisting of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j_q, j_{q}^{(q)})$, a proof `hKr` that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the bivariate sense, and integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke embeddings at auxiliary level $1$ and prime $q$. Let $P$ be a place-specialisation datum for these data, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel`, i.e. the two divisor laws and the two cusp laws at $\infty$ and $0$. Let $Q, Q'$ be places of the geometric modular function field $\overline{\mathbb{Q}}$-algebra of level $1\cdot q$ which are strict of the first kind for $P$ (the geometric Frobenius at level $1$ carries $P.\mathrm{reduceFst}$ of the place to $P.\mathrm{reduceSnd}$ of it, and its square does not fix $P.\mathrm{reduceFst}$), with $P.\mathrm{reduceFst}\,Q' = P.\mathrm{reduceFst}\,Q$ and $Q' \neq Q$, where $P.\mathrm{reduceFst}\,W$ is the specialisation under $P$ of the restriction of $W$ along the first Hecke map. Assume $P.\mathrm{reduceFst}\,Q$ is an affine geometric place (both the generator $j$ and the generator $j_N$ lie in its valuation subring) and that its evaluation at $j$ equals $a \in k$ with $a \neq 0$ and $a \neq 1728$. Let $n$ be a natural number whose image in $k$ is nonzero. Let $g$ lie in the integers of $R.R_1$ with nonzero $R.R_1$-residue, with $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$, and $\operatorname{ord}_W g = 0$ for every place $W$ strict of the first kind with $P.\mathrm{reduceFst}\,W = P.\mathrm{reduceFst}\,Q$ and $W \neq Q$, $W \neq Q'$. Finally let $e \in A$ and let $\varepsilon$ lie in the integers of $R.R_1$ with nonzero residue, such that $g = 1 + e\,\varepsilon$ (the image of $e$ taken under the structure map). The conclusion is $-1 \leq \operatorname{ord}_{P.\mathrm{reduceFst}\,Q}\bigl(R.\mathrm{residue}_1(\varepsilon)\bigr)$, the order being the negative of the logarithm of the adic valuation.
--
--   This is the auxiliary-level-one instance ($N = 1$, so the level is the prime $q$ itself) of the bound asserting that the primitive part $\varepsilon$ of a relation $g = 1 + e\varepsilon$ acquires at worst a simple pole, after reduction, at the image of a place of the first kind lying over a point with $j \neq 0, 1728$. It is obtained by passing from the prolongation tuple to the associated level-one prolongation pair, and is used in the companion bound for the second reduction and in the computation of the divisor of such a relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hQ : P.IsStrictFst Q) (hQ' : P.IsStrictFst Q') (hQQ' : P.reduceFst Q' = P.reduceFst Q) (hne : Q' ≠ Q)
    (hQaff : IsAffineGeomPlace k 1 (P.reduceFst Q))
    (a : k) (ha : (P.reduceFst Q).evalAt (jGeomGen k 1) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg₁ : g ∈ R.R₁.integers) (hg₁' : R.R₁.residue ⟨g, hg₁⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictFst W → P.reduceFst W = P.reduceFst Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (1 * q))) (hε₁ : ε ∈ R.R₁.integers) (hε₁' : R.R₁.residue ⟨ε, hε₁⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.reduceFst Q).ord (R.residue₁ ⟨ε, hε₁⟩) := by sorry
