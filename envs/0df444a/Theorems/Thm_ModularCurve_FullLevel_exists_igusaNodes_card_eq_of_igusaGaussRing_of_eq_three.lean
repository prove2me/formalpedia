-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three
-- name    : ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/87fb3023-1b5b-536a-b9f7-ecc0ede3edd1
-- title:
--   Nodes over the supersingular places on the ∞-Igusa component, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a nonunit of $A$; write $\kappa$ for the residue field of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ over $\kappa$ whose members are exactly the supersingular places, i.e. those places that are rational, affine geometric, and evaluate the geometric $j$-generator inside the supersingular $j$-set for $q$. Put $\mathrm{fieldBar}\ q\ M' = \mathrm{xHFunctionFieldBar}\ (q^2M')\ (\mathrm{levelH}\ q\ M')$, where $\mathrm{levelH}\ q\ M'$ is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, and assume the inclusion $\mathrm{hle}$ of $\mathrm{modularFunctionFieldBar}\ M'$ (the $\overline{\mathbb{Q}}$-base change of the full level-$M'$ modular function field inside Laurent series) into $\mathrm{fieldBar}\ q\ M'$. Let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\ M'$ to $\mathrm{modularFunctionFieldC}\ \kappa\ M'$, assumed coefficientwise: every Laurent series with coefficients in $A$ whose image lies in $\mathrm{modularFunctionFieldBar}\ M'$ lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and let $O^{\mathrm{Ig}}$ be a family of valuation subrings of $\mathrm{fieldBar}\ q\ M'$ indexed by the projective line over $\mathbb{Z}/q$, $O^{\mathrm{SS}}$ a family indexed by $W$. The hypotheses on these families are: $f \in O^{\mathrm{Ig}}(\infty)$ precisely when $f$ is a ratio $x/y$ of Laurent series with coefficients in $A$ whose denominator has nonzero coefficientwise reduction; every line $\ell$ is $\mathrm{redQ}\ q\ \gamma \cdot \infty$ for some $\gamma \in \Gamma_0(M')$ with $O^{\mathrm{Ig}}(\ell)$ the pullback of $O^{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$; $O^{\mathrm{Ig}}$ is injective; pullback along $\mathrm{levelAutBar}\ q\ M'\ \zeta'\ \gamma$ for $\gamma \in \Gamma_0(M')$ permutes the family $O^{\mathrm{Ig}}$; each $O^{\mathrm{SS}}(s)$ meets $\overline{\mathbb{Q}}$ exactly in $A$, is fixed by all these pullbacks, and contains an element $t$ with $t-a$ a unit of $O^{\mathrm{SS}}(s)$ for every $a \in A$; and $O^{\mathrm{SS}}(s)$ reads $R_0$ at $s$, in the sense that for $f \in R_0.\mathrm{integers}$ regular at every place of $\mathrm{modularFunctionFieldBar}\ M'$ over $\overline{\mathbb{Q}}$ at which the coefficient embedding of $jq$ is regular, if the $R_0$-residue of $f$ lies in the valuation subring of $s$ then the image of $f$ in $\mathrm{fieldBar}\ q\ M'$ lies in $O^{\mathrm{SS}}(s)$ and $f - a$ lies in the maximal ideal of $O^{\mathrm{SS}}(s)$ for every $a \in A$ whose residue is the value of $s$ at that $R_0$-residue. Finally let $R$ be a regular prolongation of $A$ from $\mathrm{fieldBar}\ q\ M'$ to $\mathrm{xHFunctionFieldC}\ \kappa\ (q^2M')\ (\mathrm{levelH}\ q\ M')$ with $R.\mathrm{integers} = O^{\mathrm{Ig}}(\infty)$, and assume $f \in R_0.\mathrm{integers}$ holds exactly when the image of $f$ in $\mathrm{fieldBar}\ q\ M'$ lies in $O^{\mathrm{Ig}}(\infty)$. The conclusion is that there exist a finite set $N^{\mathrm{Ig}}$ of places of $\mathrm{xHFunctionFieldC}\ \kappa\ (q^2M')\ (\mathrm{levelH}\ q\ M')$ over $\kappa$ with $|N^{\mathrm{Ig}}| = |W|$ and a ring homomorphism $j$ from $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ to $\mathrm{xHFunctionFieldC}\ \kappa\ (q^2M')\ (\mathrm{levelH}\ q\ M')$ such that $R$ reads $R_0$ through $j$ — for every $f \in R_0.\mathrm{integers}$ the image of $f$ lies in $R.\mathrm{integers}$ and its $R$-residue equals $j$ applied to the $R_0$-residue of $f$ — and such that a place $Q$ belongs to $N^{\mathrm{Ig}}$ exactly when there is $s \in W$ with $g$ in the valuation subring of $s$ if and only if $j(g)$ is in the valuation subring of $Q$, for all $g$.
--
--   This is the $q=3$ case of the count of nodes on the $\infty$-component of the Igusa tower: the nodes are exactly the places of the reduced Igusa field lying, via the comparison map $j$, over the supersingular places $W$ of the reduced level-$M'$ field, and there are $|W|$ of them. For $q=3$ the Igusa field at level $(q^2M', \mathrm{levelH})$ reduces to the level-$M'$ field itself, so the covering of the $\infty$-branch has degree one. It feeds the construction of the Igusa base model with its smooth point stalks and the étale coordinates at points off the branch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three
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
    ∃ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),

      NIg.card = W.card ∧

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) := by sorry
