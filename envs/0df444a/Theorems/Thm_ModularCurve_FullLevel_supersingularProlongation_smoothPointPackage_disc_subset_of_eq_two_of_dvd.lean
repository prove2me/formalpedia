-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_disc_subset_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/f35ce1fd-68f9-5755-91ca-527d3a828ffc
-- title:
--   Inclusion of smooth-point package discs, q=2 case
-- statement:
--   Fix a prime $q$ with $q=2$, a non-zero $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, and write $\kappa$ for its residue field. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ over $\kappa$ consisting exactly of the supersingular ones (rational, affine geometric, and with $\mathrm{jGeomGen}$ evaluating into $\mathrm{ssJSet}\ q$), and let $s \in W$. Assume the base-changed full level-$M'$ field $\mathrm{modularFunctionFieldBar}\ M'$ is contained in $\mathrm{fieldBar}\ q\ M'$, the base change to $\overline{\mathbb{Q}}$ of the function field of level $q^2M'$ for the kernel $H$ of reduction mod $q$. Let $R_0$ be a constant reduction of $A$ from the former to $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ whose residue map is computed by coefficientwise reduction of Laurent series, let $FSS$ be a field over $\kappa$ and $R$ a regular prolongation of $A$ to $\mathrm{fieldBar}\ q\ M'$ with residue field $FSS$, subject to: $FSS$ contains an element transcendental over $\kappa$ (h0); $R$ extends $R_0$ at $s$, for those $f$ in $R_0$'s integers regular wherever $\mathrm{jq}$ is (h1); $R$'s integers are invariant under all $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$ with $\gamma \in \Gamma_0(M')$ (h2). Let $Q$ be a place of $FSS$ over $\kappa$. Given two smooth-point packages $(S,\varphi,\chi_0,D)$ and $(S',\varphi',\chi_0',D')$ at $Q$ — each consisting of a subring of $\mathrm{fieldBar}\ q\ M'$ containing $A$, a formally smooth and formally unramified map from $A[X]$ onto it extending $A$, a residue character killing $X$, a Hensel-type unique-lift clause for sections with prescribed value of $X$, compatibility with $R$ and $Q$ with $X$ reducing to a uniformiser at $Q$, the valuation-theoretic description of the disc of rational places together with its bijection to sections, and two locality clauses (divisorial description of each local ring, a unit principle, and recovery of the subring from regularity on the disc), summarised here — the conclusion is that every place $P$ of $\mathrm{fieldBar}\ q\ M'$ over $\overline{\mathbb{Q}}$ lying in $D$ also lies in $D'$.
--
--   This is the one-sided core of the uniqueness of the smooth-point residue disc attached to a regular prolongation at a supersingular place, in the case $q=2$ with an auxiliary level divisor $\ell \equiv 11 \pmod{12}$. It is cited by [`ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_unique_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_unique_of_eq_two_of_dvd), which applies it in both directions to conclude $D = D'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_disc_subset_of_eq_two_of_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (h0 : (∃ t : FSS, Transcendental (ResidueField A) t))
    (h1 : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))))
    (h2 : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers))
    (Q : Place (ResidueField ↥A) FSS)

    (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
    (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (hpk :
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
            (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S))

    (S' : Subring ↥(fieldBar q M')) (φ' : Polynomial ↥A →+* ↥S') (χ₀' : ↥S' →+* ResidueField ↥A)
    (D' : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (hpk' :
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S') ∧
            (φ').FormallySmooth ∧ (φ').FormallyUnramified ∧
            (∀ a : ↥A, ((φ' (Polynomial.C a) : ↥(S')) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀' (φ' (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀' (φ' Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S') →+* ↥A, (∀ a : ↥A, χ (φ' (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S'), IsLocalRing.residue ↥A (χ f) = χ₀' f) ∧ χ (φ' Polynomial.X) = c) ∧
            (∀ f : ↥(S'), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀' f)) ∧
            (∃ hR : ((φ' Polynomial.X : ↥(S')) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ' Polynomial.X : ↥(S')) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D' ↔ (P.IsRational ∧ (∀ f : ↥(S'), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S'), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀' f = 0))) ∧
            (∀ χ : ↥(S') →+* ↥A, (∀ a : ↥A, χ (φ' (Polynomial.C a)) = a) →
              (∀ f : ↥(S'), IsLocalRing.residue ↥A (χ f) = χ₀' f) →
              ∃! P, P ∈ D' ∧ ∀ f : ↥(S'), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D', ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S'), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D', P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S'))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S')) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D', f ∈ P.toValuationSubring) → f ∈ S')) :
    ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ D → P ∈ D' := by sorry
