-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/ed38908a-4349-5ae3-8dda-ac9417288a6a
-- title:
--   Level-fixed component charts over a supersingular place agree
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, with residue field $\kappa =$ `ResidueField A`, and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places, i.e. those places $w$ that are rational, are affine geometric points in the sense of `IsAffineGeomPlace`, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen})\in \mathrm{ssJSet}\,q\,\kappa$. Assume $\mathrm{modularFunctionFieldBar}\,M'$, the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field inside $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$, is contained in $\mathrm{fieldBar}\,q\,M'$, the corresponding base change of the $X_H$ function field of level $q^2M'$ for $H = \mathrm{levelH}\,q\,M'$. Let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}\,\kappa\,M'$: a valuation subring $R_0.\mathrm{integers}$, a surjective residue map onto $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ with kernel the maximal ideal, compatible with $A$ and with its residue map, and a degree-preserving map on places compatible with divisors of functions. Assume further ($hR_0$) that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Fix $s \in W$. Let $F_1, F_2$ be fields, each an algebra over $\kappa$ satisfying `IsCurveOver` (principal divisors of degree zero, finite residue extensions, and $\Omega$ free of rank one) and essentially of finite type over $\kappa$, and let $C_1 : \mathrm{ComponentChart}\,A\,(\mathrm{fieldBar}\,q\,M')\,F_1$ and $C_2$ likewise for $F_2$ be component charts. Suppose that each of $O = C_1.\mathrm{integers}$ and $O = C_2.\mathrm{integers}$ satisfies: (i) for every $f \in R_0.\mathrm{integers}$ which has nonnegative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the element $\mathrm{coeffEmb}\,\overline{\mathbb{Q}}\,jq$ has nonnegative order, and whose residue $R_0.\mathrm{residue}\,f$ lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O$, and for every $a \in A$ whose residue equals the value of $R_0.\mathrm{residue}\,f$ at $s$ the difference of that image and the image of $a$ lies in the maximal ideal of $O$; and (ii) $O$ is preserved under pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for every $\zeta : \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M')$. Then $C_1.\mathrm{integers} = C_2.\mathrm{integers}$.
--
--   This is the rigidifying uniqueness step for the component of the stable model of the full-level curve lying over a chosen supersingular point in residue characteristic $2$: a valuation ring of $\mathrm{fieldBar}\,q\,M'$ that lies over $s$ in the sense of (i) and is fixed by the level automorphisms attached to $\Gamma_0(M')$ is determined, so the two charts have the same ring of integers. It is used downstream to identify Drinfeld-type rings, to transport the arithmetic Galois action to them, and to produce an isomorphism of the residue function fields of any two such charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_two_of_dvd
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
