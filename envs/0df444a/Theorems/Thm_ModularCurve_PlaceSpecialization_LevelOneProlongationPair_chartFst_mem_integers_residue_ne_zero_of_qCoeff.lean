-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_mem_integers_residue_ne_zero_of_qCoeff
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_mem_integers_residue_ne_zero_of_qCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/9a3d3156-e13a-5987-9925-64c3124c96a4
-- title:
--   q-expansion unit criterion for the ∞̄-chart
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field has characteristic $p$. Let `data` be a modular polynomial datum for $p$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(p)$ annihilating the pair of $q$-expansions $j(q), j(q^p)$) and let `hKr` be the Kronecker congruence $\Phi \equiv (Y^p - X)(Y - X^p) \bmod p$; let `hα`, `hβ` assert integrality of the two Hecke correspondence homomorphisms `heckeAlphaBar`, `heckeBetaBar` over $\overline{\mathbb{Q}}$ at level $1$ and prime $p$. Let $P$ be a place specialisation for $A$, $\ell = p$, $N = 1$ with residue data $(\mathrm{ResidueField}\,A, \mathrm{residue})$, and let $R$ be a level-one prolongation pair for $P$, so in particular $R$ supplies a regular prolongation $R_1$ from $\overline{\mathbb{Q}}$-modular functions of level $1\cdot p$ to the level-one modular function field over $\mathrm{ResidueField}\,A$. Let $S_1$ be a set of places of `modularFunctionFieldBar (1 * p)`, let $W_n$ be a finite set of places of `modularFunctionFieldC (ResidueField A) 1` whose members are exactly the supersingular places `ssPlaces p 1`, and let $\Gamma$ be a `ChartFstSupply` for $R$ and $S_1$. Let $f$ be an element of `modularFunctionFieldBar (1 * p)` all of whose Laurent coefficients lie in $A$, at least one of them being a unit of $A$. Then $f$ lies in the ring of integers of the component chart `chartFst R S₁ Wn hWn Γ` (namely $R_1$'s integers) and its image under that chart's residue map (namely $R$'s `residue₁`) is nonzero.
--
--   This is the $q$-expansion unit criterion at the chart around the reduction of the cusp $\bar\infty$: a function with $A$-integral $q$-expansion having one unit coefficient reduces to a nonzero function, i.e. is a unit for the chart's valuation ring. It is used throughout the Gauss-norm arguments that rescale families of modular functions into chart units, and is cited by the multiplicity-covering constructions (for instance in establishing integrality and Hasse-exponent bounds for such families). Only this implication holds: a chart unit need not have $A$-integral expansion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_mem_integers_residue_ne_zero_of_qCoeff.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneChartFst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_mem_integers_residue_ne_zero_of_qCoeff
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (R : P.LevelOneProlongationPair)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
    (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁)
    (f : ↥(modularFunctionFieldBar (1 * p)))
    (hf : ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A)
    (hu : ∃ n : ℤ, IsUnit (⟨(f : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hf n⟩ : ↥A)) :
    ∃ h : f ∈ (chartFst R S₁ Wn hWn Γ).integers, (chartFst R S₁ Wn hWn Γ).residue ⟨f, h⟩ ≠ 0 := by sorry
