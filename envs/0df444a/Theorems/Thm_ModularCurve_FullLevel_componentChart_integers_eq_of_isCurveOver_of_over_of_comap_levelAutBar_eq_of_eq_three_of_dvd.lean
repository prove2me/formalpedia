-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/e50c8371-b531-5794-8710-b0372cb71b4f
-- title:
--   Uniqueness of the level-fixed component chart over s (q=3)
-- statement:
--   Fix a prime $q$ with $q=3$, a level $M'\neq 0$ with $q\nmid M'$, and a prime $\ell$ with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, and write $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (the subfield of $\kappa((q))$ generated over $\kappa$ by the $j$-series and its $M'$-fold substitution) whose members are exactly the supersingular places, i.e. those places that are rational, affine geometric, and take at $\mathrm{jGeomGen}$ a value in the supersingular $j$-set $\mathrm{ssJSet}\,q\,\kappa$; fix $s\in W$. Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, the latter being the field obtained over $\overline{\mathbb Q}$ from the function field of $X_H$ of level $q^2M'$ for $H$ the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$ (units $\equiv 1 \bmod q$), the former from the full level-$M'$ modular function field. Let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}\,\kappa\,M'$, compatible with coefficientwise reduction in the sense that every Laurent series over $A$ whose image in $\overline{\mathbb Q}((q))$ lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$ and has $R_0$-residue equal to its coefficientwise reduction modulo the maximal ideal of $A$. Let $F_1,F_2$ be fields over $\kappa$ that are curves over $\kappa$ (principal divisors of degree zero, finite residue extensions, and $\Omega$ free of rank one) and essentially of finite type, and let $C_1,C_2$ be component charts of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduced fields $F_1,F_2$. Suppose that each of $O=C_1.\mathrm{integers}$ and $O=C_2.\mathrm{integers}$ satisfies: (i) for every $f\in R_0.\mathrm{integers}$ that has non-negative order at each place of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ where the image of the $j$-series $\mathrm{jq}$ has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O$, and for every $a\in A$ whose residue equals the value at $s$ of that $R_0$-residue the difference of that image and $a$ lies in the maximal ideal of $O$; and (ii) $O$ is stable under pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for every primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb Q}$ and every $\gamma\in\Gamma_0(M')$. Then $C_1.\mathrm{integers}=C_2.\mathrm{integers}$.
--
--   This is the uniqueness step in the analysis of the stable reduction of the full-level modular curve above a supersingular place: a valuation ring of $\mathrm{fieldBar}\,q\,M'$ that lies over $s$ in the sense of (i) and is fixed by the level automorphisms attached to $\Gamma_0(M')$ is determined, so any two such component charts have the same ring of integers. It is the $q=3$ form, with the rigidifying auxiliary prime $\ell\equiv 11\pmod{12}$ dividing $M'$, and is used downstream in the identification of the Drinfeld ring and of the quotient field of a chart over $s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_three_of_dvd
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
