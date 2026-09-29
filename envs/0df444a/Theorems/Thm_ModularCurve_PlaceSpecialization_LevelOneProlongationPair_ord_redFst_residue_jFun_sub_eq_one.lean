-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_redFst_residue_jFun_sub_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/c948c033-b9b4-5608-a10a-b41fa752494c
-- title:
--   Residue of j-j₀ is a uniformiser at `redFst Q`
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with a proof `hKr` that its reduction mod $q$ is the Kronecker product $(X^q - Y)(X - Y^q)$, and integrality hypotheses $h\alpha$, $h\beta$ saying that the two Hecke maps $\bar\alpha$, $\bar\beta$ at level $1$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place specialisation in this setting and $R$ a level-one prolongation pair for $P$, so in particular $R$ supplies a regular prolongation `R.R₁` of $A$ to the field `modularFunctionFieldBar (1 * q)` with residue field `modularFunctionFieldFullC (ResidueField A) 1`, and a residue map `R.residue₁` on `R.R₁.integers` with values in `modularFunctionFieldC k 1`. Let $Q$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ and $j_0 \in A$, and assume that the element $f =$ `jFun` $- \,j_0$ (the class of the $q$-expansion of $j$ minus the constant $j_0$) has $\mathrm{ord}_Q(f) > 0$ and lies in `R.R₁.integers`. Then the place `P.redFst Q` of `modularFunctionFieldC k 1`, obtained by restricting $Q$ along $\bar\alpha$ and applying the specialisation map `P.sp`, satisfies $\mathrm{ord}_{\mathrm{redFst}\,Q}\bigl(\mathrm{residue}_1(f)\bigr) = 1$.
--
--   The assertion is that the reduction of the local disc parameter $j - j_0$ at a point of the base-changed curve of level $q$ remains a uniformiser at the corresponding place of the reduced $j$-line in characteristic $q$; its content downstairs is the classification of places of the rational function field $k(\tilde\jmath)$, namely that $\tilde\jmath - a$ has a simple zero at the unique place where it vanishes. It is used in the analysis of models and strict type-one points for the level-one prolongation pair, and in the construction of suitable representatives of divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_redFst_residue_jFun_sub_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)))
    (h : (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ∈ R.R₁.integers) :
    (P.redFst Q).ord (R.residue₁ ⟨_, h⟩) = 1 := by sorry
