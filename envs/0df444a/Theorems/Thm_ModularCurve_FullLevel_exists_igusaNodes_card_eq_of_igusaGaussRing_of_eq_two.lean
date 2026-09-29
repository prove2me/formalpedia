-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_two
-- name    : ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/482d9df7-aaa2-54bd-baba-0cd1cf4bc88d
-- title:
--   Igusa nodes over the supersingular places at q=2
-- statement:
--   Fix a prime $q$ with $q=2$, a nonzero level $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$ (i.e. $q$ is a nonunit of $A$), with residue field $\kappa =$ `ResidueField A`. Let $W$ be a finite set of places of $\kappa$-field `modularFunctionFieldC κ M'` whose members are exactly the supersingular places (rational, affine geometric, with value of $j$-generator in the supersingular $j$-set). Assume `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q^2*M') (levelH q M')`, and let $R_0$ be a constant reduction of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` which, on Laurent series with coefficients in $A$, is coefficientwise reduction. Further data: an index $\zeta$ (a primitive $q$-th root of unity), a family $O^{\mathrm{Ig}}$ of valuation subrings of `fieldBar q M'` indexed by the projective line over $\mathbb{Z}/q$, and a family $O^{\mathrm{SS}}$ indexed by $W$. The hypotheses on these, summarised here, are: $O^{\mathrm{Ig}}(\infty)$ is the Gauss ring, consisting of the $f$ with $f\cdot y = x$ coefficientwise for Laurent series $x,y$ over $A$ with $y$ of nonzero reduction; every $O^{\mathrm{Ig}}(\ell)$ is the pullback of $O^{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ` for some $\gamma \in \Gamma_0(M')$ carrying $\infty$ to $\ell$ under reduction mod $q$; $O^{\mathrm{Ig}}$ is injective and is permuted by all the comaps along `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; each $O^{\mathrm{SS}}(s)$ meets $\overline{\mathbb{Q}}$ in $A$, is invariant under those comaps, admits $t$ with $t-a$ a unit for all $a \in A$, and receives elements of $R_0$'s integers whose $R_0$-residue lies at $s$, congruently to the prescribed residue values. Finally $R$ is a regular prolongation of $A$ to `fieldBar q M'` with values in `xHFunctionFieldC κ (q^2*M') (levelH q M')` whose integers are $O^{\mathrm{Ig}}(\infty)$, and membership in $R_0$'s integers is equivalent to membership in $O^{\mathrm{Ig}}(\infty)$ after inclusion. The conclusion: there is a finite set $N^{\mathrm{Ig}}$ of places of `xHFunctionFieldC κ (q^2*M') (levelH q M')` with $|N^{\mathrm{Ig}}| = |W|$, together with a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to that field such that every element of $R_0$'s integers maps into $R$'s integers with $R$-residue equal to $j$ of its $R_0$-residue, and $Q \in N^{\mathrm{Ig}}$ holds precisely when there is $s \in W$ with $g$ in the valuation subring of $s$ if and only if $j(g)$ lies in that of $Q$, for all $g$.
--
--   This is the $q=2$ instance of the count of nodes on the $\infty$-component of the Igusa tower: the places of the reduced Igusa field singled out as nodes are exactly those lying over the supersingular places $W$ of the level-$M'$ reduction, read through the map $j$ by which the regular prolongation $R$ extends the constant reduction $R_0$. It is used in the construction of smooth-point stalks for the Igusa base model and in the étale-coordinate description of off-branch stalks at $q=2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
