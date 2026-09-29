-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_jFun_jqFun
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_jFun_jqFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/0c2ecc76-0689-5621-8d5d-5d661976af97
-- title:
--   Residues of j and j(qᵖ) on the first chart
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $k = \mathrm{ResidueField}\,A$ has characteristic $p$, and suppose $p$ lies in the nonunits of $A$ (the hypothesis `hA`, i.e. $A$ lies over $p$). Let `data` be a modular polynomial datum for $p$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(p)$ annihilating the pair $(j, j_p)$ of $q$-expansions), `hKr` the Kronecker congruence $\Phi \bmod p = (X^p - Y)(X - Y^p)$, and `hα`, `hβ` the integrality of the two degeneracy embeddings $\overline{F}_1 \to \overline{F}_{1\cdot p}$ of modular function fields over $\overline{\mathbb Q}$. Let $P$ be a `PlaceSpecialization` of $A$ at $p$ in level $1$ with target field $k$ and reduction $A \to k$ the residue map, and let $R$ be a level-one prolongation pair for $P$: a pair of regular prolongations $R_1, R_2$ of $A$ to $\overline{F}_{1\cdot p}$ with residue fields inside $\mathrm{modularFunctionFieldFullC}\,k\,1$, together with a coefficientwise embedding $\iota$ into $\mathrm{modularFunctionFieldC}\,k\,1$ and the compatibilities listed in its definition. Let $S_1$ be a set of places of $\overline{F}_{1\cdot p}$, let $W_n$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,1$ whose members are exactly the supersingular places `ssPlaces p 1 k`, and let $\Gamma$ be a `ChartFstSupply` for $R$ and $S_1$, i.e. the package of sheet, pointwise and divisor laws making `chartFst R S₁ Wn hWn Γ` a component chart with integers $R_1.\mathrm{integers}$, residue $\iota \circ R_1.\mathrm{residue}$, domain the strict type-one, infinity-side and $S_1$ places, nodes $W_n$ and place map $P.\mathrm{redFst}$. The assertion is that `jFun` (the image of the $q$-expansion of $j$) and `jqFun` (the image of $j(q^p)$) both lie in the integers of this chart, that the chart residue sends `jFun` to the element $\tilde\jmath = \mathrm{jqModC}\,k$ of $\mathrm{modularFunctionFieldC}\,k\,1$ and `jqFun` to $\tilde\jmath^{\,p}$, and consequently that the residue of the difference `jqFun` $-$ `jFun`$^p$ is $0$.
--
--   This is Kronecker's congruence read on the chart of $X_0(p)$ through the cusp $\infty$: on the special fibre of that chart the two $j$-invariants are tied by $j_p = j^p$, and the tie element $j_p - j^p$ has zero residue there. It is the chart-level form of the corresponding statement for the prolongation pair, and is used in the construction of the multiplicative coverings and of the lifts of $j$ along the charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_jFun_jqFun.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_jFun_jqFun
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
    (hA : A.LiesOverPrime p) :
    ∃ (hj : PlaceSpecialization.jFun (q := p) ∈ (chartFst R S₁ Wn hWn Γ).integers)
      (hjp : PlaceSpecialization.jqFun (q := p) ∈ (chartFst R S₁ Wn hWn Γ).integers),
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, hj⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ ∧
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, hjp⟩
        = (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) ^ p ∧
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, sub_mem hjp (pow_mem hj p)⟩ = 0 := by sorry
