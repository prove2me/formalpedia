-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/c1c6e07b-656d-54b2-9c67-d5e0081d1bef
-- title:
--   Charted type II exhaustion of the supersingular tube, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a non-zero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell\equiv 11 \pmod{12}$ dividing $M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, write $\kappa$ for its residue field, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ over $\kappa$ whose members are exactly the supersingular places (rational, affine geometric, with $\mathrm{jGeomGen}$-value in $\mathrm{ssJSet}\ q\ \kappa$), and fix $s\in W$. Assume $\mathrm{modularFunctionFieldBar}\ M'\le \mathrm{fieldBar}\ q\ M'$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\ M'$ along $A$ with residue field $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ which is compatible with coefficientwise reduction of Laurent series over $A$. Let $F_{SS}$ be a $\kappa$-algebra field containing an element transcendental over $\kappa$, let $R$ be a regular prolongation of $\mathrm{fieldBar}\ q\ M'$ along $A$ with residue field $F_{SS}$, and let $C$ be a component chart along $A$ with residue field $F_{SS}$ whose ring of integers and residue map agree with those of $R$. Let $N$ be a finite set of places of $F_{SS}$ over $\kappa$ and suppose given, for each place $Q\notin N$, a set $D_Q$ of places of $\mathrm{fieldBar}\ q\ M'$ over $\overline{\mathbb{Q}}$ and an element $T_Q$ making $D_Q$ a residue disc for $R$ at $Q$ with coordinate $T_Q$ (disc coordinate, pointwise and degree conditions), with $\mathrm{dom}\,C$ equal to the union of these $D_Q$; and, for each $x\in N$, an annulus $\mathrm{An}_x$ whose modulus is non-zero, whose parameter lies in the integers of $R$ with $\mathrm{ord}_x$ of its residue equal to $1$, and which satisfies the unit principle $P(f)\cdot P(\mathrm{param})^{-\mathrm{ord}_x(\bar f)}\in A^\times$ for every $R$-integral $f$ with non-zero residue and no zeros or poles on $\mathrm{An}_x$, all $P$ in its domain. Assume the annuli are disjoint from all the discs $D_Q$ ($Q\notin N$) and pairwise disjoint, and assume the covering hypothesis that every rational place $P$ of $\mathrm{fieldBar}\ q\ M'$ over $\overline{\mathbb{Q}}$ lying in the residue tube of $s$ — that is, such that $P(f)-a$ lies in the maximal ideal of $A$ for every $f$ in the integers of $R_0$ which has non-negative order wherever the image of $\mathrm{jq}$ does and whose $R_0$-residue lies in the valuation subring of $s$, and every $a\in A$ whose residue is the value of that residue at $s$ — lies in some $D_Q$ with $Q\notin N$ or in the domain of some $\mathrm{An}_x$. Finally let $F_1$ be a $\kappa$-algebra field which is a curve over $\kappa$ (principal divisors, finite residue extensions, free rank-one module of differentials) and essentially of finite type over $\kappa$, and let $C_1$ be a component chart of $\mathrm{fieldBar}\ q\ M'$ along $A$ with residue field $F_1$ which is centred in the tube over $s$: for every $f$ in the integers of $R_0$ satisfying the same two conditions, the image of $f$ in $\mathrm{fieldBar}\ q\ M'$ lies in the integers of $C_1$, and $f-a$ lies in the maximal ideal of that ring for every $a\in A$ whose residue is the value at $s$ of the $R_0$-residue of $f$. The conclusion is a dichotomy: either every $f\in\mathrm{fieldBar}\ q\ M'$ that is integral at all places of $\mathrm{dom}\,C$ with all values in $A$ lies in the integers of $C_1$, or there is an $x\in N$ for which the same implication holds with $\mathrm{dom}\,C$ replaced by the domain of $\mathrm{An}_x$.
--
--   This is the charted form of the type II exhaustion step in the analysis of the supersingular tube of the full-level modular curve at $q=2$ over a rigid auxiliary level: a second component chart centred in the tube over the supersingular place $s$ must have its Gauss ring dominated either by the given component or by one of the node annuli. It feeds the construction of a supersingular chart together with its local affinoid and node annuli, [`ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd
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
    (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (h0 : ∃ t : FSS, Transcendental (ResidueField A) t)
    (C : ComponentChart A ↥(fieldBar q M') FSS)
    (hCR : C.integers = R.integers)
    (hCres : ∀ (f : ↥(fieldBar q M')) (hC : f ∈ C.integers) (hR : f ∈ R.integers), C.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩)
    (N : Finset (Place (ResidueField A) FSS))
    (Dx : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (T : Place (ResidueField A) FSS → ↥(fieldBar q M'))
    (hdisc : ∀ Q : Place (ResidueField A) FSS, Q ∉ N → R.IsResidueDisc Q (Dx Q) (T Q))
    (hdom : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ C.dom ↔ ∃ Q, Q ∉ N ∧ P ∈ Dx Q)
    (An : ↥N → Annulus A ↥(fieldBar q M'))
    (hatt : ∀ x : ↥N, ((An x).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
      ∃ hz : (An x).param ∈ R.integers, (x : Place (ResidueField A) FSS).ord (R.residue ⟨(An x).param, hz⟩) = 1 ∧
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ (An x).dom, P.ord f = 0) →
          ∀ P ∈ (An x).dom,
            ∃ h : P.evalAt f * (P.evalAt (An x).param) ^ (-((x : Place (ResidueField A) FSS).ord (R.residue ⟨f, hf⟩))) ∈ A,
              IsUnit (⟨_, h⟩ : A))

    (hAnD : ∀ x : ↥N, ∀ Q : Place (ResidueField A) FSS, Q ∉ N → ∀ P, P ∈ (An x).dom → P ∉ Dx Q)
    (hAnAn : ∀ x x' : ↥N, ∀ P, P ∈ (An x).dom → P ∈ (An x').dom → x = x')

    (hcover : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, IsLocalRing.residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) →
      (∃ Q, Q ∉ N ∧ P ∈ Dx Q) ∨ ∃ x : ↥N, P ∈ (An x).dom)

    (F₁ : Type) [Field F₁] [Algebra (ResidueField A) F₁]
    [IsCurveOver (ResidueField A) F₁] [Algebra.EssFiniteType (ResidueField A) F₁]
    (C₁ : ComponentChart A ↥(fieldBar q M') F₁)

    (hOs : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ C₁.integers ∧
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ C₁.integers,
              (⟨_, h⟩ : ↥C₁.integers) ∈ maximalIdeal ↥C₁.integers)) :

    (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ C₁.integers) ∨
      ∃ x : ↥N, (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An x).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ C₁.integers) := by sorry
