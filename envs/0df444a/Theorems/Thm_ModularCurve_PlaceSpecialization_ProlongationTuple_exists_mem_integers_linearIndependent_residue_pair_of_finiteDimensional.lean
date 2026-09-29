-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/6f819326-e9d1-56ee-b00c-6ed33d17b6b3
-- title:
--   Integral bases with k-independent residue pairs
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$; fix modular polynomial data `data` at level $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the $q$-expansion pair) satisfying the Kronecker congruence `hKr`, namely that the bivariate reduction of $\Phi$ modulo $q$ equals $(C X^{q}-X)(C X-X^{q})$, and integrality hypotheses `hα`, `hβ` asserting that the ring homomorphisms `heckeAlphaBar`, `heckeBetaBar` for $\overline{\mathbb Q}$, $N$, $q$ are integral. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$, so in particular $R$ carries two regular prolongations `R.R₁`, `R.R₂` of $A$ to $F=$ `modularFunctionFieldBar (N * q)` with residue maps `R.residue₁`, `R.residue₂` taking values in `modularFunctionFieldC k N`, the subfield of $\mathrm{LaurentSeries}\,k$ generated over $k$ by `jqModC k` and `jqNModC k N`. Let $V\subseteq F$ be a finite-dimensional $\overline{\mathbb Q}$-subspace of dimension $n$. Assume there is a family $b\colon \mathrm{Fin}\,n\to F$ with all $b_i\in V$, linearly independent over $\overline{\mathbb Q}$, and such that for every $i$ both the $q$-expansion of $b_i$ and that of `atkinLehnerBar N q (b i)` are, after multiplication by some nonzero scalar $c\in\overline{\mathbb Q}$, the coefficientwise image of a Laurent series with coefficients in $A$. Then there is a family $G\colon\mathrm{Fin}\,n\to F$ with every $G_i$ lying in $V$ and integral for both `R.R₁` and `R.R₂`, such that the pairs $(\,$`R.residue₁` $G_i$, `R.residue₂` $G_i)$ are linearly independent over $k$ in `modularFunctionFieldC k N` $\times$ `modularFunctionFieldC k N`.
--
--   This is the reduction step for linear systems at level $Nq$: a $\overline{\mathbb Q}$-basis of $V$ whose $q$-expansions and Atkin–Lehner transforms have, up to scalars, coefficients in $A$ is replaced by a basis of $V$ that is integral for both prolongations and whose pairs of residues remain independent over the residue field $k$. It is used in the constructions of sections of Riemann–Roch spaces with prescribed residues and orders at the two prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (V : Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) V]
    (hint : ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → ↥(modularFunctionFieldBar (N * q)),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y =
                c • ((ProlongationTuple.atkinLehnerBar N q (b i) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))) :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) V) → ↥(modularFunctionFieldBar (N * q)))
      (hG₁ : ∀ i, G i ∈ R.R₁.integers) (hG₂ : ∀ i, G i ∈ R.R₂.integers),
      (∀ i, G i ∈ V) ∧
      LinearIndependent k (fun i =>
        ((R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N)))) := by sorry
