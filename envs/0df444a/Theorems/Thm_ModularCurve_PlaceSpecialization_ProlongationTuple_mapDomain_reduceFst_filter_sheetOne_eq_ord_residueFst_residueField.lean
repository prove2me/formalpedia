-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_residueField
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/15b99d27-115b-55e5-8755-4556ff8abbed
-- title:
--   First-sheet divisor law at ordinary affine φ²-fixed places
-- statement:
--   Let $N\ge 1$, let $q$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that the image of $q$ is a non-unit of $A$; its residue field then has characteristic $q$, and the Hecke-module structures at levels $Nq$ and $N$ together with the relevant algebra structure on the level-$N$ function field over $\mathrm{ResidueField}(A)$ are in force. Assume that every non-zero element of $\mathrm{modularFunctionFieldBar}(N q)$ has a degree-zero divisor recording its orders, and fix a `ModularPolynomialData` $\mathrm{data}$ for $q$ (a monic $\Phi$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$), a Kronecker congruence $hKr$ identifying $\Phi \bmod q$ with $(\mathrm{C}X^{q}-X)(\mathrm{C}X-X^{q})$, and integrality hypotheses $h\alpha,h\beta$ for the two degeneracy maps from level $N$ to level $Nq$. Let $P$ be a place-specialisation datum for $A$, $q$, $N$ over $\mathrm{ResidueField}(A)$ with reduction the residue map of $A$, let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two branchwise divisor laws and the two cusp laws) and `OrderLawFixed`, and let $u$ be an element of $\mathrm{modularFunctionFieldBar}(Nq)$ whose Laurent expansion is the coefficientwise image of $\mathrm{modularUnitSeries}(q)=\Delta\cdot(\Delta|_{q})^{-1}$. Let $f$ lie in the valuation subring $R.R_1.\mathrm{integers}$ with $R.R_1.\mathrm{residue}(f)\neq 0$, let $D$ be a divisor with $D(W)=W.\mathrm{ord}(f)$ at every place $W$ of $\mathrm{modularFunctionFieldBar}(Nq)$, and let $v$ be a place of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}(A),N)$ fixed by the square of $\mathrm{frobOnPlacesGeomLevel}$, affine (both $j$ and $j_N$ lie in its valuation subring) and not supersingular, i.e. not in $\mathrm{ssPlaces}\,q\,N$. Then the push-forward along $P.\mathrm{reduceFst}$ of the restriction of $D$ to those $W$ whose first reduction $P.\mathrm{reduceFst}(W)$ is affine, not supersingular and fixed by the square of $\mathrm{frobOnPlacesGeomLevel}$, and at which $u$ takes a value $a\in A$ with $\mathrm{residue}(a)\neq 0$, has multiplicity at $v$ equal to $v.\mathrm{ord}(R.\mathrm{residue}_1(f))$.
--
--   This is the branchwise (first-sheet) divisor law for the reduction of $X_0(Nq)$ at $q$ with $q\nmid N$, in the form needed at the ordinary affine places of the level-$N$ fibre fixed by the square of the Frobenius correspondence: away from the supersingular points the sheet-one part of a divisor pushes down to the divisor of the first residue. It is used by the mirror statement for the second sheet and, through it, in the computation of the depth pairing and the image of the Gram map on principal divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_residueField.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_WeierstrassCurve_ReductionMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open IsLocalRing
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_residueField
    {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))] {data : ModularPolynomialData q}
      {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
      {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P)
      (hR : R.IsModel) (hO : R.OrderLawFixed) (u : modularFunctionFieldBar (N * q))
      (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
        = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)),
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
          frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v →
          IsAffineGeomPlace (ResidueField A) N v → v ∉ ssPlaces q N (ResidueField A) →
          Finsupp.mapDomain P.reduceFst
              (D.filter fun W =>
              ((frobOnPlacesGeomLevel (ResidueField A) N data hKr
                  (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst W)) = P.reduceFst W ∧
        IsAffineGeomPlace (ResidueField A) N (P.reduceFst W) ∧ P.reduceFst W ∉ ssPlaces q N (ResidueField A)) ∧
        (∃ a : A, (IsLocalRing.residue A) a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))) v
            = v.ord (R.residue₁ ⟨f, h₁⟩) := by sorry
