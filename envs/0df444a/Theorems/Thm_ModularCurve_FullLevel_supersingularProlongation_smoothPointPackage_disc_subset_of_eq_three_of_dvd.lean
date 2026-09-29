-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/87e7bcb8-5525-5eaa-b042-a2d2e5193df9
-- title:
--   Disc inclusion for two smooth-point packages, q=3
-- statement:
--   Fix a prime $q$ with $q=3$ and a nonzero natural number $M'$ with $q \nmid M'$, together with a prime $\ell$ satisfying $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$, and write $\kappa$ for its residue field. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places for $q$, that is the rational places which are affine geometric and at which the value of $\mathrm{jGeomGen}$ lies in $\mathrm{ssJSet}\,q$, and let $s \in W$. Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ inside the Laurent series field over $\overline{\mathbb{Q}}$, and let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ which is compatible with coefficientwise reduction: for every Laurent series $y$ over $A$ whose image in $\overline{\mathbb{Q}}$-coefficients lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Let $F_{ss}$ be a field over $\kappa$ and $R$ a regular prolongation of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $F_{ss}$ subject to three conditions: $F_{ss}$ contains an element transcendental over $\kappa$; $R$ lies over $s$, meaning that whenever $f$ lies in $R_0.\mathrm{integers}$ and has non-negative order at every place at which the $j$-series $\mathrm{jq}$ has non-negative order, and the $R_0$-residue of $f$ lies in the valuation subring of $s$, then the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image under $\kappa \to F_{ss}$ of the value of $R_0$-residue of $f$ at $s$; and $R.\mathrm{integers}$ is invariant under the pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for every $\zeta : \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M')$. Fix a place $Q$ of $F_{ss}$ over $\kappa$, and two data $(S,\varphi,\chi_0,D)$ and $(S',\varphi',\chi_0',D')$, each consisting of a subring of $\mathrm{fieldBar}\,q\,M'$, a ring map from $A[X]$ to it, a map to $\kappa$, and a set of places of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$, each satisfying the same list of thirteen clauses (summarised here): the subring contains the image of $A$; the map from $A[X]$ is formally smooth and formally unramified and sends constants to the image of $A$; the map to $\kappa$ sends $\varphi(C\,a)$ to the residue of $a$ and kills $\varphi(X)$; for each $c \in A$ with residue $0$ there is a unique $A$-valued section of the subring fixing the constants, reducing to the given map to $\kappa$, and sending $\varphi(X)$ to $c$; every element of the subring lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$ and reduces at $Q$ to the image of its value under the map to $\kappa$; the $R$-residue of $\varphi(X)$ has order $1$ at $Q$; the set of places consists exactly of the rational places at which every element of the subring is regular with value in $A$ and at which the value of an element has valuation $<1$ precisely when the map to $\kappa$ kills it; each $A$-valued section as above determines a unique member of this set of places whose values are the values of the section; for each such place the valuation subring is the set of quotients $g/h$ with $g,h$ in the subring and $h$ not vanishing at the place; a nonzero element with order $0$ at all these places becomes a unit of the subring after multiplication by a nonzero constant of $\overline{\mathbb{Q}}$; and any element of $R.\mathrm{integers}$ regular at all these places belongs to the subring. Then every place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ belonging to $D$ also belongs to $D'$, that is $D \subseteq D'$.
--
--   This is the one-sided core of the uniqueness of the smooth-point residue disc attached to a regular prolongation at a place $Q$ of the supersingular fibre of the full-level modular curve, in the case $q = 3$ with the auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing the level. It is used by [`ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_unique_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_unique_of_eq_three_of_dvd), which applies it twice to get $D = D'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
