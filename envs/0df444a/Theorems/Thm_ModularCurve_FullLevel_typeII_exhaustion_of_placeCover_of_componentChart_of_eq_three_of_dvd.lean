-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/5287a02f-6efa-534c-9b84-1869ecf50505
-- title:
--   Type II exhaustion of the supersingular tube, q = 3
-- statement:
--   Fix a prime $q$ with $q = 3$ and a nonzero level $M'$ with $q \nmid M'$, admitting a prime $\ell \mid M'$ with $\ell \equiv 11 \pmod{12}$; let $A \subseteq \overline{\mathbb{Q}}$ be a valuation subring with $q$ a nonunit of $A$, with residue field $\kappa = \mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ consisting exactly of the supersingular places (rational, affine geometric, with $\mathrm{jGeomGen}$-value in $\mathrm{ssJSet}\,q$), let $s \in W$, assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ via `hle`, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with target $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ whose residue is given coefficientwise on Laurent series with coefficients in $A$ (`hR₀`). Let $FSS$ be a field over $\kappa$ containing an element transcendental over $\kappa$, $R$ a regular prolongation of $\mathrm{fieldBar}\,q\,M'$ along $A$ with residue field target $FSS$, and $C$ a component chart with the same ring of integers and the same residue map as $R$. Let $N$ be a finite set of places of $FSS$ over $\kappa$ (the nodes), $Dx$ and $T$ assignments such that for every $Q \notin N$ the set $Dx\,Q$ is a residue disc for $R$ with disc coordinate $T\,Q$ (disc coordinate, pointwise and degree conditions), and such that $C.\mathrm{dom}$ is exactly the union of the $Dx\,Q$ for $Q \notin N$. Let $\mathrm{An}$ attach to each node $x \in N$ an annulus over $A$, with nonzero modulus, whose parameter is $R$-integral with $\mathrm{ord}_x$ of its $R$-residue equal to $1$, and satisfying the unit principle that for every $R$-integral $f$ with nonzero residue and order $0$ throughout the annulus domain, $P.\mathrm{evalAt}(f) \cdot (P.\mathrm{evalAt}\,\mathrm{param})^{-\mathrm{ord}_x(R.\mathrm{residue}\,f)}$ is a unit of $A$ for all $P$ in that domain; the annulus domains are assumed disjoint from all the discs $Dx\,Q$ ($Q \notin N$) and pairwise disjoint. The covering hypothesis `hcover` states that every rational place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ lying in the tube over $s$ — meaning: for every $R_0$-integral $f$ that is regular at every place where the image of $jq$ is regular and whose $R_0$-residue lies in the valuation subring of $s$, and for every $a \in A$ whose residue equals the value of that $R_0$-residue at $s$, the element $P.\mathrm{evalAt}(f) - a$ lies in the maximal ideal of $A$ — lies in some $Dx\,Q$ with $Q \notin N$ or in some annulus domain $(\mathrm{An}\,x).\mathrm{dom}$. Finally let $F_1$ be a field over $\kappa$ which is a curve over $\kappa$ (principal divisors of degree zero, finite residue extensions, module of Kähler differentials free of rank one) and essentially of finite type over $\kappa$, and $C_1$ a component chart of $\mathrm{fieldBar}\,q\,M'$ along $A$ with target $F_1$, whose ring of integers is centred in the tube over $s$ (`hOs`): every $f$ as above has image in $C_1.\mathrm{integers}$, and $f - a$ lies in the maximal ideal of $C_1.\mathrm{integers}$ whenever $\mathrm{residue}\,A\,a$ is the value of the $R_0$-residue of $f$ at $s$. The conclusion is a disjunction: either every $f \in \mathrm{fieldBar}\,q\,M'$ which lies in the valuation subring of each $P \in C.\mathrm{dom}$ with $P.\mathrm{evalAt}(f) \in A$ belongs to $C_1.\mathrm{integers}$, or there is a node $x \in N$ for which the same implication holds with $C.\mathrm{dom}$ replaced by $(\mathrm{An}\,x).\mathrm{dom}$.
--
--   This is the $q = 3$ case of the type II exhaustion step in the analysis of the stable reduction of the full-level modular curve at a supersingular point: an arbitrary component chart centred in the supersingular tube over $s$ has its ring of integers containing the Gauss ring of the given chart $C$ or of one of the node annuli, so that no further type II point can hide inside the tube. It is used by [`ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_three_of_dvd), where the auxiliary level condition $\ell \equiv 11 \pmod{12}$, $\ell \mid M'$ rigidifies the supersingular points in characteristic three.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart_of_eq_three_of_dvd
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
