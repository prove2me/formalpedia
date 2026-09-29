-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_residueField
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/84a7cdb5-2e44-58d5-ba52-89c1e47d2874
-- title:
--   Second-sheet divisor law at ordinary affine φ²-fixed places
-- statement:
--   Let $N\ge 1$, let $q$ be a prime with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; its residue field then has characteristic $q$, and the Hecke-module, decidability and algebra structures attached to $N$, $Nq$ and $A$ are those fixed by the project. Assume every non-zero element of the base-changed modular function field $\mathrm{modularFunctionFieldBar}(Nq)$ has a principal divisor of degree zero, and fix modular polynomial data for $q$ satisfying the Kronecker congruence $\Phi \equiv (C(X)^q-X)(C(X)-X^q)$ mod $q$, together with integrality of the two degeneracy embeddings $\alpha,\beta$ from level $N$ to level $Nq$. Let $P$ be a place specialisation for $A$, $q$, $N$ with coefficient field the residue field of $A$ and reduction the residue map of $A$, let $R$ be a prolongation tuple for $P$ satisfying the four model laws `IsModel` and the order law at $\varphi^2$-fixed affine places `OrderLawFixed`, and let $u$ be an element of level $Nq$ whose Laurent expansion is the coefficientwise image of $\mathrm{modularUnitSeries}\,q = \Delta\cdot(\Delta|_{q})^{-1}$. Let $f$ be integral for $R_2$ with non-zero $R_2$-residue, and let $D$ be a divisor on the level-$Nq$ curve with $D(W) = \operatorname{ord}_W f$ for every place $W$. Let $v$ be a place of the level-$N$ geometric modular function field over the residue field of $A$ which is fixed by the square of $\mathrm{frobOnPlacesGeomLevel}$, is affine (both $j$ and $j_N$ lie in its valuation subring) and is not supersingular. Then the push-forward along $P.\mathrm{reduceSnd}$ of the part of $D$ supported on those places $W$ whose second reduction $P.\mathrm{reduceSnd}\,W$ is $\varphi^2$-fixed, affine and non-supersingular and at which $\mathrm{atkinLehnerBar}\,N\,q\,(u)$ takes a value $a\in A$ with $\mathrm{residue}_A(a)\neq 0$, has multiplicity at $v$ equal to $\operatorname{ord}_v$ of the second residue of $f$.
--
--   This is the second-sheet half of the branchwise divisor law on the special fibre of $X_0(Nq)$ at $q$, the partner under the partial Atkin–Lehner involution $w_q$ of the first-sheet statement, restricted to the ordinary affine places fixed by the square of the Frobenius correspondence. It feeds the computation of depths and of the image of the Gram map used in the level-lowering argument, being cited by `depthDual_add_mem_range_gramMap_of_isPrincipal_widthChar`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_residueField.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_residueField
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
    ∀ (f : modularFunctionFieldBar (N * q)) (h₂ : f ∈ R.R₂.integers),
      R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
          frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v →
          IsAffineGeomPlace (ResidueField A) N v → v ∉ ssPlaces q N (ResidueField A) →
          Finsupp.mapDomain P.reduceSnd
              (D.filter fun W =>
              ((frobOnPlacesGeomLevel (ResidueField A) N data hKr
                  (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd W)) = P.reduceSnd W ∧
        IsAffineGeomPlace (ResidueField A) N (P.reduceSnd W) ∧ P.reduceSnd W ∉ ssPlaces q N (ResidueField A)) ∧
        (∃ a : A, (IsLocalRing.residue A) a ≠ 0 ∧ W.HasValue (ProlongationTuple.atkinLehnerBar N q u) (a :
            AlgebraicClosure ℚ)))) v
            = v.ord (R.residue₂ ⟨f, h₂⟩) := by sorry
