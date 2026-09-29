-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective
-- name    : ModularCurve.JHPlaceSpecialization.exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/ca43c4a6-d740-53a3-9356-653deafb33fe
-- title:
--   Gauss prolongation and place specialization for X_{H'}(M/p)
-- statement:
--   Fix a prime $p$ and a natural number $M\neq 0$ with $p\mid M$ but $p^{2}\nmid M$ (so $M/p\neq 0$), a subgroup $H\le(\mathbb Z/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, whose residue field $\kappa$ is of characteristic $p$ and algebraically closed. Put $F=$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, the base change to $\overline{\mathbb Q}$, inside $\overline{\mathbb Q}((q))$, of the $q$-expansion function field of level $\Gamma_{H'}(M/p)$, where $H'$ is the image of $H$ in $(\mathbb Z/(M/p))^{\times}$, and let $\bar F$ be the project's field `JHNeronObjectAtP.Fbar p M H hpM κ`, i.e. `qExpFunctionFieldC κ (ΓN p M H hpM)` inside $\kappa((q))$. The assertion is that there exist a regular prolongation $R$ of $A$ to $F$ with residue field $\bar F$ (a valuation subring `R.integers` of $F$ meeting $\overline{\mathbb Q}$ exactly in $A$, with a surjective residue map onto $\bar F$ whose kernel is the maximal ideal and which extends the residue map of $A$) and a map $\mathrm{sp}$ from places of $F/\overline{\mathbb Q}$ to places of $\bar F/\kappa$ (a place being a proper valuation subring containing the constants and having principal ideals), such that, writing reduction and inclusion of Laurent series coefficientwise via `coeffMap`: (i) $f\in$ `R.integers` if and only if $f\,y=x$ for some Laurent series $x,y$ over $A$ with $y$ of non-zero reduction; (ii) for any such witnesses, $R.\mathrm{residue}(f)\cdot\bar y=\bar x$; (iii) any $y$ over $A$ whose $q$-expansion lies in $F$ gives an element of `R.integers` with residue the coefficientwise reduction $\bar y$; (iv) for $f\in$ `R.integers` with non-zero residue, the pushforward under $\mathrm{sp}$ (via `Finsupp.mapDomain`) of the divisor of $f$ is the divisor of $R.\mathrm{residue}(f)$; (v) $\mathrm{sp}$ is the unique map with property (iv); (vi) the same divisor identity at the level of $q$-expansions, namely if $f\in F$ has $q$-expansion the image of $y$ and $g\in\bar F$, $g\neq0$, has $q$-expansion $\bar y$, then $\mathrm{sp}_*\operatorname{div}(f)=\operatorname{div}(g)$; (vii) $\mathrm{sp}$ is surjective; and (viii) for every $f\neq0$ in $F$ there is $g\neq0$ in $\bar F$ with $\mathrm{sp}_*\operatorname{div}(f)=\operatorname{div}(g)$.
--
--   This is the constant-reduction (Deuring–Roquette) specialization of the curve $X_{H'}(M/p)$, which has good reduction at $p$ because $p\nmid M/p$: the prolongation is the Gauss point of the $q$-expansions at the cusp $\infty$, its residue field is the $q$-expansion field of the same level over $\kappa$, and the induced specialization of places is compatible with divisors and unique. Clauses (vi), (vii) and (viii) are exactly the fields `d0_qexp`, `d4` and `d5` of the structure `JHPlaceSpecialization`, and the statement is used to construct such a specialization in the de Rham model of $X_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective.lean

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] :
    ∃ (R : RegularProlongation A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
          (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
      (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →
        Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),

      (∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ∈ R.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
            coeffMap A.subtype x) ∧

      (∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
        (((f : R.integers) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
          coeffMap A.subtype x →
        ((R.residue f : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) *
            coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x) ∧

      (∀ (y : LaurentSeries ↥A)
          (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
            coeffMap (IsLocalRing.residue ↥A) y) ∧

      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
          (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
          ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f)) ∧

      (∀ sp' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →
          Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
        (∀ f : R.integers, R.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
            ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp) ∧

      (∀ (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) →
        ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A),
          ((g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y →
          g ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ v, D v = v.ord f) →
          ∀ v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Finsupp.mapDomain sp D v' = v'.ord g) ∧

      Function.Surjective sp ∧

      (∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ v, D v = v.ord f) →
          ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
            ∀ v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Finsupp.mapDomain sp D v' = v'.ord g) := by sorry
