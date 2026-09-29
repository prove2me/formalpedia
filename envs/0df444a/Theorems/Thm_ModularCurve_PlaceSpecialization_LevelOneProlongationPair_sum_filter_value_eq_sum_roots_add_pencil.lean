-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add_pencil
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/6006d0f3-2707-5486-99bb-07ab900e6d8d
-- title:
--   Value-filtered pencil divisor law for j+μ j_q, μ̄≠ 0
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ with decidable equality, and a ring homomorphism $\mathrm{red}\colon A\to k$. Let `data` be modular polynomial data for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the $q$-expansion pair of $j$), `hKr` the Kronecker congruence asserting that the bivariate reduction of $\Phi$ equals $(X^q-Y)(X-Y^q)$ in the relevant normalisation, and $h\alpha,h\beta$ the integrality of the level-one Hecke maps $\bar\alpha,\bar\beta$ at $q$ over $\overline{\mathbb Q}$. Given a place specialisation $P$ for these data and a level-one prolongation pair $R$ for $P$, consisting of two regular prolongations $R_1,R_2$ of $A$ to $F=$ the level $1\cdot q$ modular function field over $\overline{\mathbb Q}$, together with residue data into the level-one function field over the residue field of $A$ and over $k$, intertwined by the Fricke involution; let $\mu\in A$ with $\mathrm{red}\,\mu\neq 0$, let $f\in F$ lie in the integers of both $R_1$ and $R_2$ with nonzero residue at each, let $D$ be the divisor on $F$ with $D(W)=\operatorname{ord}_W f$ at every place $W$ of $F$ over $\overline{\mathbb Q}$ (places being non-maximal valuation subrings containing $\overline{\mathbb Q}$ whose ideals are principal, $\operatorname{ord}$ the normalised additive valuation), and let $c_0\in k$. Then the sum of $D$ over those $W$ in the support of $D$ for which $\operatorname{ord}_W\bigl(j+\mu\, j_q-a\bigr)>0$ for some $a\in A$ with $\mathrm{red}\,a=c_0$ equals $$\sum_{a}\operatorname{ord}_{[a]}\bigl(R.\mathrm{residue}_1 f\bigr)+\sum_{b}\operatorname{ord}_{[b]}\bigl(R.\mathrm{residue}_2 f\bigr),$$ where $a$ runs over the distinct roots in $k$ of $\mathrm{red}(\mu)X^q+X-c_0$, $b$ over the distinct roots of $X^q+\mathrm{red}(\mu)X-c_0$, and $[\,\cdot\,]$ denotes the geometric place `charLGeomPlaceOfPoint` of the level-one function field over $k$ attached to a point of $k$.
--
--   This is the branch $\mathrm{red}(\mu)\neq 0$ of the pencil divisor law along the line $\overline{\mathbb Q}(j+\mu j_q)$ inside the function field of $X_0(q)$, in the form filtering places by the reduction of the single coordinate $j+\mu j_q$; the two linear factors on the right reflect the Kronecker congruence, the two prolongations corresponding to the two components of the reduction. It is used by [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_ord_pencil_eq`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_ord_pencil_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve Polynomial
open Classical in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add_pencil
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (μ : A) (hμ : red μ ≠ 0)
    (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hu₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) (c₀ : k) :
    (D.support.filter fun W => ∃ a : A, red a = c₀ ∧
        0 < W.ord (jFun (q := q)
              + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))).sum D
      = ((Polynomial.C (red μ) * Polynomial.X ^ q + Polynomial.X - Polynomial.C c₀).roots.toFinset.sum
            fun a => (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, h₁⟩))
        + ((Polynomial.X ^ q + Polynomial.C (red μ) * Polynomial.X - Polynomial.C c₀).roots.toFinset.sum
            fun b => (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, h₂⟩)) := by sorry
