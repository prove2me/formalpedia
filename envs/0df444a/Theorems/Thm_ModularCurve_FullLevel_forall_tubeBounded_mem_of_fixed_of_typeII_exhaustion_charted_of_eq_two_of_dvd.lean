-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/61ae1df5-8b95-51a6-b4a4-df89ec297bd2
-- title:
--   Level-fixed charted rings over a supersingular place contain the affinoid
-- statement:
--   Fix a prime $q$ with $q = 2$, a nonzero level $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, and write $\kappa = \mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\,q\,M'\,\kappa$ (rational affine geometric places at which $\mathrm{jGeomGen}$ evaluates into $\mathrm{ssJSet}\,q$), and let $s \in W$. Assume the intermediate fields of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ satisfy $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with reduced field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ — a valuation subring $R_0.\mathrm{integers}$, a surjective residue map with kernel the maximal ideal, a map on places preserving degrees, compatible with $A$ — which is moreover coefficientwise: every Laurent series $y$ over $A$ whose image in $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$, with residue the coefficientwise reduction of $y$. Let $C$ be a component chart of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduced field a $\kappa$-algebra $F_{ss}$, and let $\mathrm{An} : E \to \mathrm{Annulus}\,A\,(\mathrm{fieldBar}\,q\,M')$ be a family of annuli. Call a function $f$ bounded on a set $D$ of places if $f \in P.\mathrm{toValuationSubring}$ and $P.\mathrm{evalAt}\,f \in A$ for all $P \in D$, and call a component chart $C_o$ centred at $s$ if for every $f \in R_0.\mathrm{integers}$ whose order is $\ge 0$ at every place of $\mathrm{modularFunctionFieldBar}\,M'$ where the embedded $j$-expansion $\mathrm{jq}$ has order $\ge 0$, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $C_o.\mathrm{integers}$ and, for every $a \in A$ whose residue is the value of the $R_0$-residue of $f$ at $s$, the difference $f - a$ lies in the maximal ideal of $C_o.\mathrm{integers}$. Three hypotheses are assumed: (exhaustion) for every field $F_o$ that is an essentially finite type $\kappa$-algebra and a curve over $\kappa$ and every component chart $C_o$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduced field $F_o$ centred at $s$, either all functions bounded on $C.\mathrm{dom}$ lie in $C_o.\mathrm{integers}$, or all functions bounded on $(\mathrm{An}\,e).\mathrm{dom}$ do for some $e \in E$; (move) for every $e$ there are a primitive $q$-th root of unity index $\zeta$ and $\gamma \in \Gamma_0(M')$ such that the pullback of $\mathrm{An}\,e$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ has the same domain as $\mathrm{An}\,e'$ for some $e' \ne e$; (separation) any valuation subring $O$ of $\mathrm{fieldBar}\,q\,M'$ that prolongs $A$, contains an element $t$ with $t - a$ a unit of $O$ for all $a \in A$, does not contain all functions bounded on $C.\mathrm{dom}$, and contains all functions bounded on $(\mathrm{An}\,e).\mathrm{dom}$ and on $(\mathrm{An}\,e').\mathrm{dom}$, forces $e = e'$. The conclusion: for every field $F_o$ as above and every component chart $C_o$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduced field $F_o$ which is centred at $s$ and whose ring of integers is invariant under pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for all $\zeta$ and all $\gamma \in \Gamma_0(M')$, every function bounded on $C.\mathrm{dom}$ lies in $C_o.\mathrm{integers}$.
--
--   This is the type-II step in the local analysis of the semistable model of the full-level modular curve at the prime $2$ with rigid auxiliary level: a residually transcendental chart centred at a supersingular point and stable under all level automorphisms cannot be supported on one of the node annuli, since the level automorphisms move each annulus to a different one while separation allows only one. It is used by [`ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_two_of_dvd) to identify the ring of integers of such a chart with the supersingular affinoid algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted_of_eq_two_of_dvd
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
