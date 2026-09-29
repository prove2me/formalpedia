-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted
-- name    : ModularCurve.FullLevel.forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/362af305-dd32-5ef2-901c-d1e3eef34d09
-- title:
--   Level-fixed charts over a supersingular place are affinoid-bounded
-- statement:
--   Fix a prime $q\ge 5$, a nonzero level $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$; let $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in $\mathrm{ssJSet}$), let $\mathrm{hle}$ be the inclusion $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with residue field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ such that every Laurent series with coefficients in $A$ whose image lies in $\mathrm{modularFunctionFieldBar}\,M'$ is an $R_0$-integer with $R_0$-residue the coefficientwise reduction, and let $s\in W$. Let $C$ be a component chart of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduction field $FSS$, and $An:E\to\mathrm{Annulus}\,A\,(\mathrm{fieldBar}\,q\,M')$ a family of annuli. For a valuation subring or chart of integers $O$ write $R_C\subseteq O$ for: every $f$ with $f\in P$'s valuation subring and $P.\mathrm{evalAt}\,f\in A$ for all $P\in C.\mathrm{dom}$ lies in $O$, and likewise $R_e\subseteq O$ with $An\,e$ in place of $C$. Call a component chart $Co$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ centred at $s$ if for every $R_0$-integer $f$ of $\mathrm{modularFunctionFieldBar}\,M'$ that is regular at every place where $jq$ is regular and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ lies in $Co.\mathrm{integers}$, and for each $a\in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue the difference $f-a$ lies in the maximal ideal of $Co.\mathrm{integers}$. Assume: (exhaustion) for every field $Fo$ that is a $\kappa$-algebra, a curve over $\kappa$ and essentially of finite type over $\kappa$, and every component chart $Co$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduction field $Fo$ centred at $s$, either $R_C\subseteq Co.\mathrm{integers}$ or $R_e\subseteq Co.\mathrm{integers}$ for some $e\in E$; (motion) for each $e$ there are $\zeta\in\mathrm{Idx}\,q$, $\gamma\in\Gamma_0(M')$ and $e'\neq e$ with the domain of the pullback of $An\,e$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ equal to $An\,e'.\mathrm{dom}$; (separation) if a valuation subring $O$ of $\mathrm{fieldBar}\,q\,M'$ prolongs $A$ (its intersection with $\overline{\mathbb{Q}}$ is $A$), contains some $t$ with $t-a$ a unit of $O$ for every $a\in A$, does not contain $R_C$, and contains both $R_e$ and $R_{e'}$, then $e=e'$. The conclusion: for every such field $Fo$ and every component chart $Co$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduction field $Fo$ that is centred at $s$ and whose ring of integers is invariant under all $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma\in\Gamma_0(M')$, one has $R_C\subseteq Co.\mathrm{integers}$.
--
--   This is the charted form of the statement that a residually transcendental point of the modular curve lying over a supersingular place and fixed by all level automorphisms must lie in the supersingular affinoid rather than in one of the annuli joining it to the rest of the special fibre; the annuli are permuted without fixed index by the level automorphisms, and the separation hypothesis forbids a single point from lying over two of them. It is used in the identification of the ring of integers of such a fixed chart with that of the affinoid chart $C$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted
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
    (C : ComponentChart A (fieldBar q M') FSS)
    {E : Type} (An : E → Annulus A ↥(fieldBar q M'))

    (hexh : ∀ (Fo : Type) (_ : Field Fo) (_ : Algebra (ResidueField A) Fo)
        (_ : IsCurveOver (ResidueField A) Fo) (_ : Algebra.EssFiniteType (ResidueField A) Fo)
        (Co : ComponentChart A (fieldBar q M') Fo),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ Co.integers ∧
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ Co.integers,
              (⟨_, h⟩ : Co.integers) ∈ maximalIdeal Co.integers) →
        (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ Co.integers) ∨ ∃ e : E, (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An e).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ Co.integers))

    (hmove : ∀ e : E, ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ ∃ e' : E, e' ≠ e ∧
        ((An e).comap (levelAutBar q M' ζ γ)).dom = (An e').dom)

    (hsep : ∀ (O : ValuationSubring ↥(fieldBar q M')) (e e' : E),
        (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A) →
        (∃ t : ↥(fieldBar q M'), t ∈ O ∧ ∀ a : A,
          ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O, IsUnit (⟨_, h⟩ : O)) →
        ¬ (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) →
        (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An e).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) →
        (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An e').dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) → e = e') :
    ∀ (Fo : Type) (_ : Field Fo) (_ : Algebra (ResidueField A) Fo)
      (_ : IsCurveOver (ResidueField A) Fo) (_ : Algebra.EssFiniteType (ResidueField A) Fo)
      (Co : ComponentChart A (fieldBar q M') Fo),
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ Co.integers ∧
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ Co.integers,
              (⟨_, h⟩ : Co.integers) ∈ maximalIdeal Co.integers) →
      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → Co.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = Co.integers) →
      (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ Co.integers) := by sorry
