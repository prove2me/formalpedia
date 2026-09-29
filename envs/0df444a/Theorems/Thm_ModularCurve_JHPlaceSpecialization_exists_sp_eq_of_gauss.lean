-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_sp_eq_of_gauss
-- name    : ModularCurve.JHPlaceSpecialization.exists_sp_eq_of_gauss
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/d7e1a6e5-5652-57ea-a264-91897327a186
-- title:
--   Gauss specialisation inhabits the J_H place-specialisation structure
-- statement:
--   Fix a prime $p$ and a non-zero $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $H'$ be the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ under `ZMod.unitsMap`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (so $A$ lies over $p$), whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F' = \overline{\mathbb{Q}}\,(\text{the } q\text{-expansion field } X_{H'}(M/p))$ for the base change `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` inside $\overline{\mathbb{Q}}$-Laurent series, and $\bar F' =$ `Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for the group `ΓN p M H hpM`. Let $R$ be a regular prolongation of $A$ to $F'$ with residue field $\bar F'$, that is: a valuation subring `R.integers` of $F'$ meeting $\overline{\mathbb{Q}}$ exactly in $A$, together with a surjective ring homomorphism `R.residue` onto $\bar F'$ whose kernel is the maximal ideal, compatible with reduction on $A$, and such that every non-zero $f \in F'$ has a scalar multiple integral with non-zero residue. Let $\mathrm{sp}$ be any map from places of $F'/\overline{\mathbb{Q}}$ to places of $\bar F'/\kappa$. Assume: (i) `R.integers` is the Gauss ring, namely $f$ is integral exactly when $f\,y = x$ for some Laurent series $x,y$ with coefficients in $A$ with the coefficientwise reduction of $y$ non-zero; (ii) for such a presentation of an integral $f$, the residue of $f$, read as a Laurent series over $\kappa$, times the reduction of $y$ equals the reduction of $x$; (iii) for every integral $f$ with non-zero residue and every divisor $D$ with $D(P) = \mathrm{ord}_P(f)$ for all $P$, the pushforward `Finsupp.mapDomain sp D` satisfies $(\mathrm{sp}_*D)(Q) = \mathrm{ord}_Q(\mathrm{res}\,f)$ for all $Q$; (iv) $\mathrm{sp}$ is the unique map with property (iii); (v) every Laurent series with coefficients in $A$ which lies in $F'$ is integral, with residue the coefficientwise reduction; (vi) $\mathrm{sp}$ is surjective; (vii) $\mathrm{sp}$ is invariant under the semilinear action of the inertia subgroup of $A$ over $\mathbb{Q}$, via `arithmeticGalois`; and (viii) for $\sigma$ a Frobenius at $A$ for $p$ (that is, $\sigma$ lies in the decomposition group and acts on $\kappa$ by $x \mapsto x^p$), $\mathrm{sp}(\sigma \bullet w)$ is the restriction of $\mathrm{sp}(w)$ along the $p$-power $q$-expansion Frobenius `qExpFrobeniusPlaceModL`. Then there is a term of the structure `JHPlaceSpecialization p M H hpM A` whose underlying map of places is $\mathrm{sp}$; that is, $\mathrm{sp}$ can be completed by a homomorphism $\mathrm{Pic}^0(F') \to \mathrm{Pic}^0(\bar F')$ compatible with $\mathrm{sp}_*$ on degree-zero divisors, and satisfies the $q$-expansion divisor law, surjectivity, the statement that the pushforward of the divisor of any non-zero $f$ is the divisor of some non-zero element of $\bar F'$, and the two Galois laws for inertia and Frobenius.
--
--   This is the packaging step for the reduction of modular function fields at a place above $p$: it records that the Gauss specialisation of places, reduction of $q$-expansions coefficientwise, satisfies all the axioms of the place-specialisation structure attached to $J_H$ at $p$. It is used in the construction of the de Rham model at $p$ of $X_H$, where the specialisation structure, prolongation data and component-group information are assembled for a place of the function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_sp_eq_of_gauss.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.exists_sp_eq_of_gauss
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (R : RegularProlongation A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (hgauss : ∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ∈ R.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (hres : ∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
      (((f : R.integers) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
      ((R.residue f : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y =
        coeffMap (IsLocalRing.residue ↥A) x)

    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
        ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f))

    (huniq : ∀ sp' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
          ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp)

    (hq : ∀ (y : LaurentSeries ↥A)
      (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hsurj : Function.Surjective sp)
    (hinert : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) = sp w))
    (hfrob : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (sp w)))
    :
    ∃ Psp : JHPlaceSpecialization p M H hpM A, Psp.sp = sp := by sorry
