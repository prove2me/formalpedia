-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_ord_pencil_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/3ae8b5bd-0bc8-552b-9c52-714a3695d4ef
-- title:
--   Summed divisor law for the pencil j+μ j_q
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$; fix data $\mathrm{data}$ consisting of a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$, a proof $h_{Kr}$ that the bivariate reduction of $\Phi$ modulo $q$ equals $(X^q-Y)(X-Y^q)$, and proofs $h_\alpha,h_\beta$ that the level-$1$, prime-$q$ Hecke maps $\overline\alpha,\overline\beta$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data and $R$ a `LevelOneProlongationPair` for $P$, consisting of two regular prolongations $R_1,R_2$ of $A$ to $\mathrm{modularFunctionFieldBar}(1\cdot q)$ with residue field the level-one full modular function field over the residue field of $A$, together with the compatibility data of the structure (lift $\overline{\mathrm{red}}$ of $\mathrm{red}$, the embedding $\iota$ into the level-one function field over $k$, reduction of Laurent coefficients, and the identification of $R_2$ with $R_1$ composed with the Fricke involution). Let $f$ lie in the integers of both $R_1$ and $R_2$ with nonzero residues there, let $D$ be a divisor on the places of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$ with $D(W)=\mathrm{ord}_W f$ for every place $W$, let $\mu\in A$ satisfy $\mathrm{red}\,\mu\neq 0$ or $\mu=0$, and let $c\in k$. Then the sum of $D$ over those $W$ in the support of $D$ for which there exist $x,y\in A$ with $\mathrm{red}\,x+\mathrm{red}\,\mu\cdot\mathrm{red}\,y=c$, $\mathrm{ord}_W(\,j-x)>0$ and $\mathrm{ord}_W(\,j_q-y)>0$ (with $j$, $j_q$ the functions `jFun`, `jqFun`) equals $\sum_a \mathrm{ord}_{a}\bigl(R.\mathrm{residue}_1\,f\bigr)+\sum_b \mathrm{ord}_{b}\bigl(R.\mathrm{residue}_2\,f\bigr)$, where $a$ runs without multiplicity over the roots in $k$ of $\mathrm{red}(\mu)T^q+T-c$, $b$ over the roots of $T^q+\mathrm{red}(\mu)T-c$, the residues of $f$ at $R_1$ and $R_2$ are taken in the level-one modular function field over $k$, and $\mathrm{ord}_a$ denotes the order at the place `charLGeomPlaceOfPoint k a` of that field.
--
--   This is the divisor law for the pencil of maps $W\mapsto j(W)+\mu\,j_q(W)$ on $X_0(q)$, summed over both components of the reduction of $X_0(q)$ modulo $q$: by the Kronecker congruence the fibre over a residue class $c$ meets the first component in the roots of $\mathrm{red}(\mu)T^q+T=c$ and the second in the roots of $T^q+\mathrm{red}(\mu)T=c$. It is used in the proof of `divisorLawFst`, which isolates the contribution of the first component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_ord_pencil_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hu₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (μ : A) (hμ : red μ ≠ 0 ∨ μ = 0) (c : k) :
    (D.support.filter fun W => ∃ x y : A, red x + red μ * red y = c ∧
        0 < W.ord (jFun (q := q) - algebraMap _ _ (x : AlgebraicClosure ℚ)) ∧
        0 < W.ord (jqFun (q := q) - algebraMap _ _ (y : AlgebraicClosure ℚ))).sum D
    = ((Polynomial.C (red μ) * Polynomial.X ^ q + Polynomial.X - Polynomial.C c).roots.toFinset.sum
          fun a => (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, h₁⟩))
      + ((Polynomial.X ^ q + Polynomial.C (red μ) * Polynomial.X - Polynomial.C c).roots.toFinset.sum
          fun b => (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, h₂⟩)) := by sorry
