-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue
-- name    : ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/84f15f4b-120b-504b-87a4-380682549d10
-- title:
--   Igusa Gauss ring prolongation compatible with constant reduction
-- statement:
--   Fix a prime $q\ge 5$, a positive integer $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$; write $\kappa$ for its residue field. Let $W$ be a finite set of places of $\kappa_C(M')=\kappa(j_q,\,j_q\!\circ\! q^{M'})$ over $\kappa$ whose members are exactly the supersingular places `ssPlaces q M'` (rational affine geometric places at which $j$ is supersingular), and assume the inclusion `hle` of the base-changed level-$M'$ field $\overline{\mathbb Q}\cdot F(X(M'))$ inside $\overline{\mathbb Q}\cdot F(\Gamma_H(q^2M'))$, where $H$ is the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$. Let $R_0$ be a constant reduction of $A$ from the base-changed level-$M'$ field to $\kappa_C(M')$ (a valuation subring with surjective residue map onto $\kappa_C(M')$ having the maximal ideal as kernel, lying over $A$, together with a place map preserving degrees and orders), pinned coefficientwise by `hR₀`: every Laurent series over $A$ lying in the base-changed field is $R_0$-integral with $R_0$-residue the coefficientwise reduction. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb Q}$, and let $O^{Ig}_\ell$ ($\ell$ in the projective line over $\mathbb Z/q$) and $O^{SS}_s$ ($s\in W$) be valuation subrings of $\overline{\mathbb Q}\cdot F(\Gamma_H(q^2M'))$. The hypotheses on these are: $O^{Ig}_{\infty}$ consists exactly of the ratios $x/y$ of Laurent series over $A$ with $y$ having nonzero reduction (the Gauss ring condition), each $O^{Ig}_\ell$ is a pullback of $O^{Ig}_{\infty}$ along `levelAutBar q M' ζ γ` for some $\gamma\in\Gamma_0(M')$ with $\bar\gamma\cdot\infty=\ell$, $\ell\mapsto O^{Ig}_\ell$ is injective, and the family is permuted by all `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$; each $O^{SS}_s$ meets $\overline{\mathbb Q}$ in $A$, is fixed by all `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$, contains an element $t$ with $t-a$ a unit for every $a\in A$, and satisfies the specialisation compatibility `hSS_over`: for $R_0$-integral $f$ whose order is nonnegative at every place of the base-changed level-$M'$ field where the coefficient image of $j_q$ has nonnegative order and whose $R_0$-residue lies in the valuation ring of $s$, the image of $f$ lies in $O^{SS}_s$ and $f-a$ lies in the maximal ideal of $O^{SS}_s$ whenever the residue of $a\in A$ equals the value of the $R_0$-residue of $f$ at $s$. Finally let $R$ be a regular prolongation of $A$ from $\overline{\mathbb Q}\cdot F(\Gamma_H(q^2M'))$ to the concrete field $\kappa_C(\Gamma_H(q^2M'))$ with $R.\mathrm{integers}=O^{Ig}_{\infty}$, and assume `hR₀O`: $f$ is $R_0$-integral precisely when its image lies in $O^{Ig}_{\infty}$. The conclusion asserts the existence of a regular prolongation $R'$ of $A$ from $\overline{\mathbb Q}\cdot F(\Gamma_H(q^2M'))$ to $\kappa_C(\Gamma_H(q^2M'))$ with $R'.\mathrm{integers}=O^{Ig}_{\infty}$ and such that every $R_0$-integral $f$ has $R'$-integral image whose $R'$-residue, read as a Laurent series over $\kappa$, is the $R_0$-residue of $f$ read as a Laurent series over $\kappa$.
--
--   This is the statement that the Igusa Gauss ring at level $q^2M'$ carries a regular prolongation of the place $A$ whose reduction map restricts on the level-$M'$ subfield to the given constant reduction $R_0$, both being coefficientwise reduction of $q$-expansions. It is used in the count of nodes on the Igusa components, [`ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing`](thm.html#ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing); the existence of the prolongation itself and of the Igusa valuation subrings comes from [`ModularCurve.FullLevel.exists_igusaValuationSubrings`](thm.html#ModularCurve.FullLevel.exists_igusaValuationSubrings), so the content added here is the compatibility with $R_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
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

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue
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
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))
    :
    ∃ R' : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      R'.integers = OIg (lineInfty q) ∧
      ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R'.integers,
          ((R'.residue ⟨_, hC⟩ : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
              LaurentSeries (ResidueField A)) =
            ((R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) := by sorry
