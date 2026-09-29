-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/06cc4c66-45eb-532f-b2c0-08141dbd7ca4
-- title:
--   First-sheet divisor law at ordinary φ²-fixed places
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ and an algebraically closed field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} : A \to k$; assume principal divisors exist on $F =$ `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot q$. Let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence `hKr`, let `hα`, `hβ` be the integrality hypotheses for the two degeneracy maps from level $1$ to level $1\cdot q$, let $P$ be a place specialisation in this situation, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`. Let $u \in F$ have Laurent expansion the coefficientwise image of `modularUnitSeries q`, that is $\Delta$ divided by its $q$-fold $q$-expansion. The assertion is: for every $f \in F$ lying in the valuation subring `R.R₁.integers` whose first residue `R.R₁.residue` is non-zero, every divisor $D$ with $D(W) = \operatorname{ord}_W f$ for all places $W$ of $F$, and every place $v$ of `modularFunctionFieldC k 1` such that $\varphi^2(v) = v$ for $\varphi =$ `frobOnPlacesGeomLevel k 1 data hKr`, such that both moduli generators $j$ and $j_N$ lie in the valuation subring of $v$, and such that $v$ is not a supersingular place (not rational-affine with $j$-value in `ssJSet q k`), one has $$\sum_{W} D(W) = \operatorname{ord}_v\big(R.\mathrm{residue}_1\,f\big),$$ the sum being over those places $W$ of $F$ with $P.\mathrm{reduceFst}\,W = v$ which satisfy both: $P.\mathrm{reduceFst}\,W$ is $\varphi^2$-fixed, affine and not supersingular, and $u$ has a value at $W$ equal to the image of some $a \in A$ with $\mathrm{red}\,a \neq 0$. Compared with `DivisorLawFst`, the hypotheses on $f$ are one-sided (no integrality or non-vanishing is required on the second sheet), the guard that $v$ is not $\varphi^2$-fixed is replaced by $v$ being $\varphi^2$-fixed, affine and ordinary, and the strict-first filter is replaced by the first-sheet filter defined by the unit values of $u$.
--
--   This is the branchwise divisor law on the first sheet of $X_0(q)$ above an ordinary, $\varphi^2$-fixed affine point of the $j$-line in characteristic $q$: push-forward under the first reduction of the part of $\operatorname{div} f$ carried by the first-sheet disc computes the order of the first residue. It is used for the level-one first- and second-sheet divisor laws and in the computation of the component-group projection of the depth pairing at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k] [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) :
    ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place k (modularFunctionFieldC k 1),
          frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
          IsAffineGeomPlace k 1 v → v ∉ ssPlaces q 1 k →
          Finsupp.mapDomain P.reduceFst
              (D.filter fun W => ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W ∧
        IsAffineGeomPlace k 1 (P.reduceFst W) ∧ P.reduceFst W ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))) v
            = v.ord (R.residue₁ ⟨f, h₁⟩) := by sorry
