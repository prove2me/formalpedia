-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue_of_eq_three
-- name    : ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/60ec4ea5-14ab-5960-bc06-307cdf4612ef
-- title:
--   Regular prolongation onto the Igusa Gauss ring, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$, a natural number $M' \neq 0$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ belongs to the nonunits of $A$; write $\kappa$ for its residue field. Let $W$ be a finite set of places of $\kappa$-intermediate field $\mathrm{modularFunctionFieldC}\,\kappa\,M' = \kappa(j, j_{M'}) \subseteq \kappa((q))$ whose members are exactly the supersingular places, i.e. those that are rational, affine geometric and send the geometric $j$-generator into the supersingular $j$-set. Assume the intermediate field $\mathrm{modularFunctionFieldBar}\,M'$ (the $\overline{\mathbb Q}$-base change of the full level-$M'$ function field inside $\overline{\mathbb Q}((q))$) is contained in $\mathrm{fieldBar}\,q\,M'$, the $\overline{\mathbb Q}$-base change of the function field of level $q^2M'$ with subgroup $\mathrm{levelH}\,q\,M'$, the kernel of $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$. Let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (a valuation subring contracting to $A$, a surjective residue map onto the target with kernel the maximal ideal, compatible with $A \to \kappa$, together with scaling and place-pushforward data), pinned coefficientwise: every Laurent series over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral with $R_0$-residue the coefficientwise reduction. Fix a primitive $q$-th root of unity $\zeta$ and families $O^{\mathrm{Ig}}$ indexed by the projective line over $\mathbb Z/q$ and $O^{\mathrm{SS}}$ indexed by $W$, of valuation subrings of $\mathrm{fieldBar}\,q\,M'$, subject to: $O^{\mathrm{Ig}}(\infty)$ is the Gauss ring, consisting of the $f$ with $f\,y = x$ for Laurent series $x, y$ over $A$ with $y$ of nonzero coefficientwise reduction; each $O^{\mathrm{Ig}}(\ell)$ is the pullback of $O^{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma \in \Gamma_0(M')$ carrying $\infty$ to $\ell$; $O^{\mathrm{Ig}}$ is injective; pullback along any $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$ permutes the family; each $O^{\mathrm{SS}}(s)$ contracts to $A$, is fixed by all such pullbacks, contains an element $t$ with $t - a$ a unit for every $a \in A$, and satisfies the compatibility that an $R_0$-integral $f$ which is regular wherever the $j$-series is regular and whose $R_0$-residue is $s$-integral has image in $O^{\mathrm{SS}}(s)$, with $f - a$ in the maximal ideal whenever the residue of $a \in A$ is the value at $s$ of the $R_0$-residue of $f$. Assume finally a regular prolongation $R$ of $A$ from $\mathrm{fieldBar}\,q\,M'$ onto $\mathrm{xHFunctionFieldC}\,\kappa\,(q^2M')\,(\mathrm{levelH}\,q\,M')$ with $R.\mathrm{integers} = O^{\mathrm{Ig}}(\infty)$, and that $R_0$-integrality of $f$ is equivalent to membership of its image in $O^{\mathrm{Ig}}(\infty)$. Then there is a regular prolongation $R'$ of $A$ from $\mathrm{fieldBar}\,q\,M'$ onto $\mathrm{xHFunctionFieldC}\,\kappa\,(q^2M')\,(\mathrm{levelH}\,q\,M')$ with $R'.\mathrm{integers} = O^{\mathrm{Ig}}(\infty)$ such that every $R_0$-integral $f$ has image $R'$-integral, and the $R'$-residue of that image, read as a Laurent series over $\kappa$, equals the $R_0$-residue of $f$ read as a Laurent series over $\kappa$.
--
--   This is the $q = 3$ case of the statement that the Gauss ring of the $\infty$-branch of the Igusa tower carries a regular prolongation whose residue map, on functions of level $M'$, agrees with the level-$M'$ constant reduction read coefficientwise on $q$-expansions; the conclusion thus normalises the given prolongation $R$ so that its reduction is $q$-expansion reduction. It is used in the count of the nodes of the Igusa components over the supersingular places at $q = 3$, via [`ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three), and it draws on [`ModularCurve.FullLevel.exists_igusaValuationSubrings_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_igusaValuationSubrings_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue_of_eq_three.lean

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

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
