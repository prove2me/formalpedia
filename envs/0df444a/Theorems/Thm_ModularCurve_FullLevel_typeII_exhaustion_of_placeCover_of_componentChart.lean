-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart
-- name    : ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/65f29a47-449a-531e-83fb-da9b7deb8b94
-- title:
--   Type-II exhaustion of the supersingular tube, charted form
-- statement:
--   Fix a prime $q\ge 5$ and a nonzero $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ (i.e. $q$ is a nonunit of $A$), with residue field $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places (rational, affine geometric, with value of $\mathrm{jGeomGen}$ in $\mathrm{ssJSet}\,q$), and let $s\in W$. Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with residue field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ such that every Laurent series with coefficients in $A$ lying in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral with $R_0$-residue the coefficientwise reduction. Let $FSS$ be a field over $\kappa$ containing an element transcendental over $\kappa$, $R$ a regular prolongation of $\mathrm{fieldBar}\,q\,M'$ along $A$ with residue field $FSS$, and $C$ a component chart with the same ring of integers as $R$ and the same residue map on it. Let $N$ be a finite set of places of $FSS$ over $\kappa$; assume that for each place $Q\notin N$ the set $Dx\,Q$ of places of $\mathrm{fieldBar}\,q\,M'$ with coordinate $T\,Q$ is a residue disc for $R$ at $Q$ (disc coordinate, pointwise and degree conditions), and that $C.\mathrm{dom}$ is exactly the union of the $Dx\,Q$ for $Q\notin N$. For each $x\in N$ let $An\,x$ be an annulus over $A$ in $\mathrm{fieldBar}\,q\,M'$ whose modulus is nonzero, whose parameter is $R$-integral with $\mathrm{ord}_x$ of its residue equal to $1$, and which satisfies the unit principle normalised at $x$: for $R$-integral $f$ with nonzero residue and $\mathrm{ord}_P f=0$ on the annulus domain, $P.\mathrm{evalAt}\,f\cdot (P.\mathrm{evalAt}\,\mathrm{param})^{-\mathrm{ord}_x(R.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there, for all $P$ in that domain. Assume the annulus domains are disjoint from every $Dx\,Q$ with $Q\notin N$ and pairwise disjoint. Assume furthermore a place-cover hypothesis: every rational place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ such that, for every $R_0$-integral $f$ in $\mathrm{modularFunctionFieldBar}\,M'$ which is regular at every place where $\mathrm{jq}$ is regular and whose $R_0$-residue lies in the valuation subring of $s$, and every $a\in A$ whose residue equals the value at $s$ of that $R_0$-residue, one has $P.\mathrm{evalAt}$ of the image of $f$ minus $a$ in the maximal ideal of $A$, lies in some $Dx\,Q$ with $Q\notin N$ or in some $(An\,x).\mathrm{dom}$. Finally let $F_1$ be a field over $\kappa$ which is a curve over $\kappa$ (principal divisors, finite residue extensions, $\Omega_{F_1/\kappa}$ free of rank one) and essentially of finite type over $\kappa$, and let $C_1$ be a component chart of $\mathrm{fieldBar}\,q\,M'$ along $A$ with residue field $F_1$ which is centred in the tube over $s$: for every $R_0$-integral $f$ as above with $R_0$-residue in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $C_1.\mathrm{integers}$, and for every $a\in A$ whose residue is the value at $s$ of the $R_0$-residue, the difference of that image and $a$ lies in the maximal ideal of $C_1.\mathrm{integers}$. The conclusion is the alternative: either every $f$ in $\mathrm{fieldBar}\,q\,M'$ that is integral with value in $A$ at all places of $C.\mathrm{dom}$ lies in $C_1.\mathrm{integers}$, or there is an $x\in N$ for which the same holds with $C.\mathrm{dom}$ replaced by $(An\,x).\mathrm{dom}$.
--
--   This is the charted form of the type-II exhaustion step in the analysis of the semistable reduction of the modular curve of full level $q$ over a valuation ring above $q$: a valuation ring presented as the Gauss ring of a component chart centred in the supersingular tube over $s$ must dominate either the affinoid attached to the given component chart or one of the node annuli. It feeds [`ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted`](thm.html#ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart.lean

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

theorem ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
