-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt
-- name    : ModularCurve.JHPlaceSpecialization.sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/a09dcaa1-053b-5213-be76-ca00713e1ca9
-- title:
--   Galois behaviour of the Gauss specialisation of places
-- statement:
--   Fix a prime $p$ and a natural number $M\neq 0$ with $p\mid M$ and $p^{2}\nmid M$, a subgroup $H\le(\mathbb Z/M)^{\times}$, and assume $M/p\neq 0$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ (`LiesOverPrime`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the $q$-expansion field of level $(M/p,\,H$ pushed forward along `ZMod.unitsMap`$)$, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion field over $\kappa$ for the subgroup `JHNeronObjectAtP.ΓN p M H hpM` of $\mathrm{SL}_2(\mathbb Z)$. Let $R$ be a regular prolongation of $A$ from $\overline{\mathbb Q}$ to $F$ with residue field $\bar F$, and $\mathrm{sp}$ a map from places of $F/\overline{\mathbb Q}$ to places of $\bar F/\kappa$, subject to four hypotheses: `hgauss`, that $R$'s integers are exactly those $f\in F$ expressible as a ratio $x/y$ of Laurent series with coefficients in $A$ whose denominator has nonzero reduction; `hres`, that for such a representation the Laurent series of $R.\mathrm{residue}\,f$ times the reduction of $y$ is the reduction of $x$; `hdiv`, that $\mathrm{sp}$ pushes the divisor of any $f$ in $R$'s integers with nonzero residue (given as a finitely supported function agreeing with $P\mapsto \mathrm{ord}_P f$) to the divisor of $R.\mathrm{residue}\,f$; and `huniq`, that $\mathrm{sp}$ is the only such map. The conclusion is the conjunction of two assertions: first, for every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ lying in the image of the inertia subgroup of $A$ and every place $w$ of $F$, $\mathrm{sp}$ of the translate of $w$ by the semilinear automorphism `arithmeticGalois` attached to $\sigma$ (coefficientwise action of $\sigma$ on $q$-expansions) equals $\mathrm{sp}(w)$; second, for every $\sigma$ that is a Frobenius at $A$ for $q=p$, i.e. lies in the decomposition group of $A$ and acts on $\kappa$ as $x\mapsto x^{p}$, $\mathrm{sp}$ of that translate equals `qExpFrobeniusPlaceModL`$(\kappa,\,$`ΓN`$,\,p)$ applied to $\mathrm{sp}(w)$, namely the restriction of $\mathrm{sp}(w)$ along the $q$-expansion Frobenius endomorphism of $\bar F$.
--
--   This is the Galois-equivariance part of Deuring's theory of reduction of a function field modulo a prime of the constant field, in the form needed for the Eichler–Shimura congruence relation: inertia acts trivially on the specialised places, and an arithmetic Frobenius at $A$ induces the $q$-expansion Frobenius on places of the reduced function field. It supplies the `d6_inertia` and `d6_frobenius` clauses of a `JHPlaceSpecialization`, and is used in the construction of the de Rham model data at $p$ for $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt.lean

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt
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
          ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp) :
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) = sp w) ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (sp w)) := by sorry
