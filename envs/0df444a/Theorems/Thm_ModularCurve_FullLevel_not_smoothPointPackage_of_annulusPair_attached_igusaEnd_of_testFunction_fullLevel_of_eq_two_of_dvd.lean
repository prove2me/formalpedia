-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_not_smoothPointPackage_of_annulusPair_attached_igusaEnd_of_testFunction_fullLevel_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.not_smoothPointPackage_of_annulusPair_attached_igusaEnd_of_testFunction_fullLevel_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/42a63e61-47f6-5eba-9d66-83a445a4e464
-- title:
--   No smooth-point package at an Igusa-end node, q=2
-- statement:
--   Fix a prime $q$ with $q=2$, a level $M'\neq 0$ with $q\nmid M'$, and a prime $\ell$ with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$; let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)(M')$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\,q\,M'$ (rational, affine-geometric, with $j$-value in the supersingular set), and let $s\in W$. Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to that characteristic-$q$ function field which is compatible with coefficientwise reduction: every Laurent series over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral and its $R_0$-residue, read as a Laurent series over $\mathrm{ResidueField}\,A$, is its coefficientwise reduction. Let $R$ and $R_x$ be regular prolongations of $A$ from $\mathrm{fieldBar}\,q\,M'$ to fields $F_{SS}$, $F_I$ over $\mathrm{ResidueField}\,A$, with places $x$ of $F_{SS}$ and $b_x$ of $F_I$. Let $An,An'$ be annuli over $A$ in $\mathrm{fieldBar}\,q\,M'$ with the same domain and the same modulus, the modulus nonzero and in $\mathfrak m_A$, and with reciprocal parameters: $An'.\mathrm{param}\cdot An.\mathrm{param}$ is the image of the modulus. Assume: $An.\mathrm{param}$ is $R_x$-integral with $b_x$-order $1$ of its residue, and every $R_x$-integral $f$ with nonzero residue and $\mathrm{ord}_P f=0$ on $An.\mathrm{dom}$ satisfies that $P.\mathrm{evalAt}\,f\cdot (P.\mathrm{evalAt}\,An.\mathrm{param})^{-b_x.\mathrm{ord}(\overline f)}$ is a unit of $A$ for all $P\in An.\mathrm{dom}$; the same with $(An',R,x)$ in place of $(An,R_x,b_x)$; two places of $An.\mathrm{dom}$ at which $An.\mathrm{param}$ has distinct $A$-valuations; and the tube condition: for each $P\in An.\mathrm{dom}$, each $R_0$-integral $f$ integral wherever the $j$-series $\mathrm{jq}$ is and with $R_0$-residue in the valuation subring of $s$, and each $a\in A$ whose residue is $s.\mathrm{evalAt}$ of that residue, $P.\mathrm{evalAt}(f)-a$ lies in $\mathfrak m_A$. Finally let $g\neq 0$ in $\mathrm{fieldBar}\,q\,M'$ be integral at every place where $\mathrm{jq}$ is, $R$-integral with $R$-residue $0$, with $g,g^{-1}$ both $R_x$-integral, and $\mathrm{ord}_P g=0$ on $An.\mathrm{dom}$. Then for no subring $S\subseteq \mathrm{fieldBar}\,q\,M'$, ring map $\varphi:A[X]\to S$, ring map $\chi_0:S\to\mathrm{ResidueField}\,A$ and set $D$ of places of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ do the following fifteen conditions hold simultaneously: $S$ contains the image of $A$; $\varphi$ is formally smooth and formally unramified; $\varphi(C\,a)$ is the image of $a$ and $\chi_0(\varphi(C\,a))$ is the residue of $a$, for $a\in A$; $\chi_0(\varphi(X))=0$; for each $c\in A$ with residue $0$ there is exactly one ring map $\chi:S\to A$ splitting $\varphi\circ C$, reducing to $\chi_0$ and sending $\varphi(X)$ to $c$; every $f\in S$ is $R$-integral with $R$-residue in the valuation subring of $x$ whose reduction there is the image of $\chi_0 f$; $\varphi(X)$ is $R$-integral with $x$-order of its residue equal to $1$; $D$ consists exactly of the rational places $P$ with all $f\in S$ in the valuation subring of $P$ and $P.\mathrm{evalAt}\,f\in A$, and $A.\mathrm{valuation}(P.\mathrm{evalAt}\,f)<1$ if and only if $\chi_0 f=0$; every $\chi$ as above comes from a unique $P\in D$ by evaluation; for $P\in D$, membership of $f$ in the valuation subring of $P$ is equivalent to $f$ being a quotient of elements of $S$ with nonvanishing denominator at $P$; every nonzero $f$ with $\mathrm{ord}_P f=0$ on $D$ becomes a unit of $S$ after multiplication by a nonzero constant; every $R$-integral $f$ lying in all valuation subrings of $D$ belongs to $S$; and $\mathrm{ord}_P\ge 0$ on $D$ for the $j$-series.
--
--   This is the $q=2$ instance, at a rigid auxiliary level controlled by the auxiliary prime $\ell\equiv 11\pmod{12}$, of the obstruction statement saying that a reciprocal annulus pair attached to an Igusa end inside the tube of a supersingular place $s$ cannot be covered by a residue-disc (smooth-point) chart; the test function $g$ lives on the full-level field. It is used in the construction of semistable coverings and node presentations for the full modular curve at $q=2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_not_smoothPointPackage_of_annulusPair_attached_igusaEnd_of_testFunction_fullLevel_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.not_smoothPointPackage_of_annulusPair_attached_igusaEnd_of_testFunction_fullLevel_of_eq_two_of_dvd
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
    (x : Place (ResidueField ↥A) FSS)

    (FI : Type) [Field FI] [Algebra (ResidueField A) FI]
    (Rx : RegularProlongation A (fieldBar q M') FI) (bx : Place (ResidueField A) FI)

    (An An' : Annulus A ↥(fieldBar q M'))
    (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hm0 : ((An.modulus : ↥A) : AlgebraicClosure ℚ) ≠ 0) (hm𝔪 : (An.modulus : ↥A) ∈ maximalIdeal ↥A)
    (hrec : An'.param * An.param = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((An.modulus : ↥A) : AlgebraicClosure ℚ))
    (hfar : (∃ hz : An.param ∈ Rx.integers, bx.ord (Rx.residue ⟨An.param, hz⟩) = 1 ∧
      ∀ (f : ↥(fieldBar q M')) (hf : f ∈ Rx.integers), Rx.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
        ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(bx.ord (Rx.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (hnear : (∃ hz : An'.param ∈ R.integers, x.ord (R.residue ⟨An'.param, hz⟩) = 1 ∧
      ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
        ∀ P ∈ An'.dom,
          ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(x.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hrad : ∃ P ∈ An.dom, ∃ P' ∈ An.dom, A.valuation (P.evalAt An.param) ≠ A.valuation (P'.evalAt An.param))

    (htube : ∀ P ∈ An.dom, (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, IsLocalRing.residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A))

    (g : ↥(fieldBar q M')) (hg0 : g ≠ 0)
    (hgcF : ∀ P' : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
      0 ≤ P'.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) →
        0 ≤ P'.ord g)
    (hgR : g ∈ R.integers) (hgres : R.residue ⟨g, hgR⟩ = 0)
    (hgRx : g ∈ Rx.integers) (hginv : g⁻¹ ∈ Rx.integers)
    (hzf : ∀ P ∈ An.dom, P.ord g = 0) :
    ∀ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
      (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
      ¬ (
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
            (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ x.toValuationSubring,
              IsLocalRing.residue ↥x.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) x.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              x.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) ∧

            (∀ P ∈ D, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')))) := by sorry
