-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/6b90153b-6570-57e7-aa1d-a48f6d90f4a0
-- title:
--   First-sheet divisor law at ordinary fixed places, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$), and integrality hypotheses `hα`, `hβ` for the two degeneracy maps $\overline{\mathbb{Q}}$-embedding level $1$ into level $1\cdot q$; assume principal divisors exist in `modularFunctionFieldBar (1 * q)`. Let $P$ be a place specialisation of these data, $R$ a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`, and let $u$ be an element of `modularFunctionFieldBar (1 * q)` whose Laurent expansion is the coefficientwise image of `modularUnitSeries q` $= \Delta\text{-series} \cdot (q\text{-expansion of }\Delta\text{-series})^{-1}$. The assertion is: for every $f$ in `R.R₁.integers` with non-zero $R_1$-residue, every divisor $D$ with $D(W) = \operatorname{ord}_W f$ for all places $W$, and every place $v$ of `modularFunctionFieldC k 1` fixed by the square of `frobOnPlacesGeomLevel`, affine in the sense that both $j$ and the level generator lie in its valuation subring, and not in `ssPlaces q 1 k`, the push-forward along `P.reduceFst` of the part of $D$ supported on those $W$ whose reduction `P.reduceFst W` is fixed by that square, affine and non-supersingular and at which $u$ takes a value $a \in A$ with $red\,a \neq 0$, evaluated at $v$, equals $\operatorname{ord}_v$ of `R.residue₁ ⟨f, h₁⟩`.
--
--   This is the branchwise divisor law on the first sheet of $X_0(q)$ over $k$ at an ordinary place of the special fibre fixed by the square of Frobenius: only the places of the first branch contribute, and their contribution computes the order of the first residue of $f$. It feeds the collection of first-chart laws (`chartFstLaws_sheetOne_of_isModel`) and the existence statement `exists_hasValue_residueFst_of_sheetOne_levelOne`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k]
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
