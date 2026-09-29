-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFstLaws_sheetOne_of_isModel
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFstLaws_sheetOne_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/79d849d1-77ec-59bb-9757-c2b228abf7d4
-- title:
--   Chart laws for the sheet cut out by the modular unit
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $k =$ `ResidueField A` has characteristic $p$, together with: modular polynomial data `data` for $p$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(p)$ annihilating the pair of $q$-expansions $j(q), j(q^{p})$), a proof `hKr` of the Kronecker congruence $\Phi \equiv (X^{p}-Y)(X-Y^{p}) \bmod p$, integrality `hα`, `hβ` of the two degeneracy maps from level $1$ to level $p$ over $\overline{\mathbb{Q}}$, a place specialisation $P$ of level $1$ at $p$ with residue map $A \to k$, a level-one prolongation pair $R = (R_1,R_2)$ for $P$, and the hypothesis `hR` that $R$ is a model, i.e. satisfies both divisor laws and the two cusp laws at $\bar\infty$ and $\bar 0$. Let $u$ be an element of the geometric modular function field of level $1\cdot p$ whose Laurent expansion is the modular unit series $\Delta(q)/\Delta(q^{p})$. Then the chart laws `ChartFstLaws` hold for $R$ and the set $S_1$ of those places $W$ for which the reduction $P.\mathrm{redFst}\,W$ is fixed by the square of the geometric-level Frobenius on places, is affine (both $j$ and $j_N$ generators lie in its valuation subring), is not a supersingular place, and for which $u$ has at $W$ a value $a \in A$ with nonzero residue. Explicitly: these three conditions hold for all $W \in S_1$; for every $f$ in the valuation subring $R_1.\mathrm{integers}$ with nonzero residue, every divisor $D$ with $D\,W = \operatorname{ord}_W f$ and every place $v$ of the level-one geometric function field over $k$ fixed by the squared Frobenius, affine and not supersingular, the pushforward along $P.\mathrm{redFst}$ of $D$ restricted to $S_1$ takes at $v$ the value $\operatorname{ord}_v$ of the $R_1$-residue of $f$; and for $W \in S_1$ and $f \in R_1.\mathrm{integers}$ lying in the valuation subring of every $W' \in S_1$ with the same reduction as $W$, there is $c \in A$ such that $f$ has value $c$ at $W$ and the $R_1$-residue of $f$ has value $\mathrm{res}(c)$ at $P.\mathrm{redFst}\,W$.
--
--   This is the verification, for a level-one prolongation pair, of the sheet and chart laws of the $\bar\infty$-component of the special fibre of $X_0(p)$ at $p$, on the sheet singled out by the unit $\Delta(q)/\Delta(q^{p})$; the geometric content is that the two components of the Deligne–Rapoport model meet only at the supersingular points. It is used in the construction of separated chart coverings for the multiplicative covering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFstLaws_sheetOne_of_isModel.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneChartFst
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFstLaws_sheetOne_of_isModel
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel)
    (u : ↥(modularFunctionFieldBar (1 * p)))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p)) :
    R.ChartFstLaws {W | ((frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W ∧
        IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W) ∧ P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A)) ∧
        (∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))} := by sorry
