-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_reduceFst_residue_jFun_sub_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_reduceFst_residue_jFun_sub_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/053a4735-e07d-5fac-8e1a-59e8183de543
-- title:
--   Residue of j-j₀ is a uniformiser downstairs
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$ with $q \nmid N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; let `data` be a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the $q$-modular pair, `hKr` the Kronecker congruence that $\Phi$ mod $q$ equals $(\,\mathrm C\,X^{q} - X)(\mathrm C\,X - X^{q})$, and `hα`, `hβ` the integrality of the two Hecke maps from level $N$ to level $Nq$ over $\overline{\mathbb Q}$. Let $P$ be a `PlaceSpecialization` for these data and $R$ a `ProlongationTuple` over $P$. Let $Q$ be a place of the level-$Nq$ modular function field over $\overline{\mathbb Q}$, and $j_0 \in A$ such that the function $j - j_0$ (the element `jFun N q` minus the constant $j_0$) has $\operatorname{ord}_Q > 0$. Let $a \in k$ be the value at the reduced place $P.\mathrm{reduceFst}\,Q$ — the place of the level-$N$ modular function field over $k$ obtained by restricting $Q$ along `heckeAlphaBar` and applying $P.\mathrm{sp}$ — of the $j$-function `jGeomGen k N`, and assume $a \neq 0$ and $a \neq 1728$. Assume finally that $j - j_0$ lies in the integers of $R.R_1$. Then its image under `residue₁` has $\operatorname{ord} = 1$ at $P.\mathrm{reduceFst}\,Q$, i.e. it is a uniformiser there.
--
--   This is the level-$N$ form of the assertion that the reduction of the disc parameter $j - j_0$ is a uniformiser at the corresponding place of the first copy of the special fibre, which reflects the unramifiedness of $X_0(N)_k \to X(1)_k$ at places whose $j$-value avoids $0$ and $1728$ when $q \nmid N$. It is used in the verification of the model conditions, in the lower bound for the order of the first residue of a function of the form $1 + (\,\cdot\,)$ at such places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_reduceFst_residue_jFun_sub_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_reduceFst_residue_jFun_sub_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) (R : P.ProlongationTuple)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (j₀ : A) (hj₀ : 0 < Q.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (j₀ : AlgebraicClosure ℚ)))
    (a : k) (ha : (P.reduceFst Q).evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (h : (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (j₀ : AlgebraicClosure ℚ)) ∈ R.R₁.integers) :
    (P.reduceFst Q).ord (R.residue₁ ⟨_, h⟩) = 1 := by sorry
