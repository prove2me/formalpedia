-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_integers_snd_residue_jFun_sub_ne_zero
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_integers_snd_residue_jFun_sub_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/b805ecc6-ea69-5c7f-9b36-e3e18df10f78
-- title:
--   The parameter j-j₀ has nonzero second residue
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions) together with a proof `hKr` that its bivariate reduction modulo $q$ equals $(X^q-Y)(X-Y^q)$, and integrality hypotheses `hα`, `hβ` for the Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $1$ and prime $q$. Let $P$ be a place-specialisation datum for these data and $R$ a level-one prolongation pair for $P$: this packages a residue homomorphism $\mathrm{ResidueField}\,A \to k$ lifting $red$, a coefficientwise map $\iota$ of level-one modular function fields, and two regular prolongations $R_1, R_2$ of $A$ to $\mathrm{modularFunctionFieldBar}(1\cdot q)$ with residue field the level-one modular function field over $\mathrm{ResidueField}\,A$, subject to the axioms that $R_1$-residues are coefficientwise reductions of $A$-integral Laurent series, that $R_2$ is the transport of $R_1$ along the Fricke involution (both for integrality and for residues), and that $R_1$ is compatible with the characteristic-$q$ modular reduction homomorphism through $\iota$. Then for every $j_0 \in A$ the element `jFun` $-\ j_0$ of $\mathrm{modularFunctionFieldBar}(1\cdot q)$, where `jFun` is the $j$-invariant viewed in that field and $j_0$ is mapped in by the structure morphism, lies in $R_2$'s valuation subring of integers, and its $R_2$-residue is nonzero.
--
--   This asserts that the local parameter $t = j - j_0$ at a point of $X_0(q)$ is not merely $R_2$-integral but an $R_2$-unit, the second residue being the reduction of $j_q = w_q j$ minus $\overline{j_0}$. Combined with the corresponding statement for $R_1$ it makes $t$ a common unit of both prolongations of the pair, and it is used in determining the order of vanishing of $j - j_0$ at type-one places and in the construction of admissible representatives of divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_integers_snd_residue_jFun_sub_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_integers_snd_residue_jFun_sub_ne_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    (j₀ : A) :
    ∃ h : (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ∈ R.R₂.integers,
      R.R₂.residue ⟨_, h⟩ ≠ 0 := by sorry
