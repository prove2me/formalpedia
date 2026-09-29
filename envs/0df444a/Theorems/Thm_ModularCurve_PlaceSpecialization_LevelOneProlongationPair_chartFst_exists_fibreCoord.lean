-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/61eeee83-ed6a-5e41-bf6b-e4ec23ec7cae
-- title:
--   Fibre coordinates on the first component chart of X₀(p)
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field has characteristic $p$, and write $k = \mathrm{ResidueField}(A)$. Let `data` supply a monic bivariate integral modular polynomial $\Phi$ of degree $\psi(p)$ vanishing at $(j,j_p)$, let `hKr` assert the Kronecker congruence $\Phi \equiv (X^p-Y)(X-Y^p)$ after reduction, and let `hα`, `hβ` assert that the Hecke maps $\bar\alpha$, $\bar\beta$ at level $1$ and prime $p$ are integral ring homomorphisms. Let $P$ be a place specialisation over $A$ at level $1$ with target field $k$ and reduction the residue map of $A$, assume $p$ lies in the nonunits of $A$, let $R$ be a level-one prolongation pair for $P$, let $S_1$ be a set of places of $\overline{\mathbb Q}$-modular function field of level $1\cdot p$, let `Wn` be a finite set of places of the level-one residue function field $k$-field whose members are exactly the supersingular places `ssPlaces p 1 k`, and let $\Gamma$ be a `ChartFstSupply` for $R$ and $S_1$. Write $C$ for the component chart `chartFst R S₁ Wn hWn Γ`, with integers $R.R_1$.`integers`, residue map $R$.`residue₁`, domain `chartFstDom P S₁`, nodes `Wn` and place map $P$.`redFst`. Then there is an assignment $x \mapsto T_x$ from places of the level-one $k$-function field to elements of the level-$1\cdot p$ function field over $\overline{\mathbb Q}$ such that for every $W$ in the domain of $C$, putting $x = P.\mathrm{redFst}(W)$ and $t = T_x - T_x(W)$ (the value $T_x(W) = W.\mathrm{evalAt}(T_x) \in \overline{\mathbb Q}$ being mapped in by the structure map), one has $t \in C$.`integers`, the residue of $t$ is nonzero, $\mathrm{ord}_x$ of that residue equals $1$, $\mathrm{ord}_W(t) > 0$, and $\mathrm{ord}_Q(t) = 0$ for every $Q \neq W$ in the domain of $C$ with $P.\mathrm{redFst}(Q) = x$.
--
--   The functions $t$ produced here serve as local fibre coordinates on the first (ordinary) component chart of $X_0(p)$ along $A$: each is a chart-integral function whose reduction is a uniformiser at the given point of the residue line and which vanishes at exactly one place of the chart domain above that point. The statement is used in [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneChartFst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField ↥A) p] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (hA : A.LiesOverPrime p) (R : LevelOneProlongationPair P)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (Wn : Finset (Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)))
    (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (IsLocalRing.ResidueField ↥A)) (Γ : R.ChartFstSupply S₁) :
    ∃ T : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) →
        ↥(modularFunctionFieldBar (1 * p)),
    ∀ W ∈ (chartFst R S₁ Wn hWn Γ).dom,
    ∃ h : T ((chartFst R S₁ Wn hWn Γ).placeMap W)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (W.evalAt (T ((chartFst R S₁ Wn hWn Γ).placeMap W)))
          ∈ (chartFst R S₁ Wn hWn Γ).integers,
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩ ≠ 0 ∧
      ((chartFst R S₁ Wn hWn Γ).placeMap W).ord ((chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩) = 1 ∧
      0 < W.ord (T ((chartFst R S₁ Wn hWn Γ).placeMap W)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (W.evalAt (T ((chartFst R S₁ Wn hWn Γ).placeMap W)))) ∧
      ∀ Q ∈ (chartFst R S₁ Wn hWn Γ).dom, (chartFst R S₁ Wn hWn Γ).placeMap Q = (chartFst R S₁ Wn hWn Γ).placeMap W →
        Q ≠ W →
        Q.ord (T ((chartFst R S₁ Wn hWn Γ).placeMap W)
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
              (W.evalAt (T ((chartFst R S₁ Wn hWn Γ).placeMap W)))) = 0 := by sorry
