-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq
-- name    : ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/c6ad1655-fa26-5f74-9aff-c428d3f8f6e8
-- title:
--   Uniqueness of level-fixed component charts over a supersingular place
-- statement:
--   Fix a prime $q \ge 5$ and a level $M' \neq 0$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, residue field $\kappa =$ `ResidueField A`. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ whose members are exactly the supersingular places (rational, affine geometric, with $\mathrm{jGeomGen}$-value in $\mathrm{ssJSet}\,q$), let $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ whose residue computes coefficientwise reduction of Laurent series with coefficients in $A$, and let $s \in W$. Let $F_1, F_2$ be fields over $\kappa$ that are curves over $\kappa$ (principal divisors, finite residue extensions, differentials free of rank one) and essentially of finite type, with component charts $C_i : \mathrm{ComponentChart}\,A\,(\mathrm{fieldBar}\,q\,M')\,F_i$. Assume that each of $O = C_1.\mathrm{integers}$, $C_2.\mathrm{integers}$ satisfies: (i) every $f$ in $R_0.\mathrm{integers}$ with $\mathrm{ord}_P f \ge 0$ at every place $P$ where the $q$-expansion of $j$ has non-negative order, and with $R_0$-residue in the valuation subring of $s$, has its image in $\mathrm{fieldBar}\,q\,M'$ in $O$, and for each $a \in A$ whose residue is the value at $s$ of that $R_0$-residue the difference $f - a$ lies in the maximal ideal of $O$; (ii) $O$ is stable under pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for every primitive $q$-th root of unity index $\zeta$ and every $\gamma \in \Gamma_0(M')$. Then $C_1.\mathrm{integers} = C_2.\mathrm{integers}$.
--
--   This is the uniqueness (fixed-point) step in the construction of the semistable model of the full-level modular curve at a supersingular point: a valuation ring coming from a component chart, lying over the supersingular place $s$ and fixed by the level automorphisms attached to $\Gamma_0(M')$, is determined. It is used in the subsequent identification of the Drinfeld ring and the component at $s$, and in the comparison of charts under the arithmetic Galois action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq.lean

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

theorem ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq
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
    (F₁ : Type) [Field F₁] [Algebra (ResidueField A) F₁] [IsCurveOver (ResidueField A) F₁]
    [Algebra.EssFiniteType (ResidueField A) F₁] (C₁ : ComponentChart A (fieldBar q M') F₁)
    (F₂ : Type) [Field F₂] [Algebra (ResidueField A) F₂] [IsCurveOver (ResidueField A) F₂]
    [Algebra.EssFiniteType (ResidueField A) F₂] (C₂ : ComponentChart A (fieldBar q M') F₂)
    (hO : ∀ O ∈ ({C₁.integers, C₂.integers} : Set (ValuationSubring (fieldBar q M'))),

      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ O ∧
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O,
              (⟨_, h⟩ : O) ∈ maximalIdeal O) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → O.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = O)) :
    C₁.integers = C₂.integers := by sorry
