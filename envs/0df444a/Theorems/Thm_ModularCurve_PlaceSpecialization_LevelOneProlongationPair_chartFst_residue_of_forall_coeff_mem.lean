-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_of_forall_coeff_mem
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_of_forall_coeff_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f2c285f1-6859-55ff-8f3f-714c820fc8e7
-- title:
--   Integral q-expansions and coefficientwise residue in the first chart
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field has characteristic $p$. Let `data` be a modular polynomial datum for $p$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(p)$ vanishing on the pair $(j(q),j(q^p))$), `hKr` the Kronecker congruence $\overline\Phi=(X^p-Y)(X-Y^p)$ for it, and $h\alpha,h\beta$ the integrality of the two Hecke ring homomorphisms $\overline\alpha,\overline\beta$ at level $1$ and prime $p$. Let $P$ be a place-specialisation datum over $A$ at level $1$ with target field the residue field $k$ of $A$ and reduction the residue map $A\to k$, and $R$ a level-one prolongation pair for $P$; let $S_1$ be a set of places of $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot p}$, $W_n$ a finite set of places of the level-one function field $F_C(k)$ equal (by `hWn`) to the set of supersingular places `ssPlaces p 1 k`, and $\Gamma$ a supply of chart laws for $R$ and $S_1$. Let $f\in\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot p}$ have all Laurent coefficients $a_n$ in $A$. Then $f$ lies in the ring of integers of the chart `chartFst R S₁ Wn hWn Γ`, i.e. in `R.R₁.integers`, and its residue, viewed as a Laurent series over $k$, has $n$-th coefficient the residue class of $a_n$ for every $n\in\mathbb Z$.
--
--   This is the $q$-expansion form of integrality for the chart at $\bar\infty$: membership in the Gauss-type prolongation attached to the $q$-expansion is guaranteed by $A$-integrality of the coefficients, and reduction of the chart is then coefficientwise reduction of the expansion. It is used repeatedly in the construction of the multiplicative covering and of the charts' residue computations, for instance in checking that explicit $q$-series are chart-integral with non-zero residue and in linear-independence arguments for families of such residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_of_forall_coeff_mem.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_of_forall_coeff_mem
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
    (hf : ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A) :
    ∃ h : f ∈ (chartFst R S₁ Wn hWn Γ).integers, ∀ n : ℤ,
      (((chartFst R S₁ Wn hWn Γ).residue ⟨f, h⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
          LaurentSeries (ResidueField ↥A)).coeff n =
        IsLocalRing.residue ↥A ⟨(f : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hf n⟩ := by sorry
