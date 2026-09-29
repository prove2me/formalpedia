-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing
-- name    : ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/97d588b5-e974-5bbb-ba7d-abe022d01a07
-- title:
--   Nodes of the ∞-Igusa component over the supersingular places
-- statement:
--   Let $q \ge 5$ be a prime, let $M'$ be a nonzero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, with residue field $\kappa =$ `ResidueField A`. Let $W$ be a finite set of places of $\kappa$ in `modularFunctionFieldC κ M'` whose members are exactly the supersingular places, i.e. the rational affine geometric places at which the value of `jGeomGen κ M'` lies in `ssJSet q κ`. Assume the base-changed full level-$M'$ field `modularFunctionFieldBar M'` is contained in $\mathcal{F} =$ `fieldBar q M'`, the base change to $\overline{\mathbb{Q}}$ of the function field of level $\Gamma_H(q^2M')$ for $H$ the kernel of $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $R_0$ be a constant reduction of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` (a valuation subring with surjective residue map onto the latter, kernel the maximal ideal, compatible with $A$ and with orders of divisors), assumed to act coefficientwise: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that element lies in $R_0$'s integers and its residue, viewed as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$. Let $O^{\mathrm{Ig}}$ assign a valuation subring of $\mathcal{F}$ to each point of $\mathbb{P}^1(\mathbb{Z}/q)$ and $O^{\mathrm{SS}}$ one to each $s \in W$, subject to: (i) $f \in O^{\mathrm{Ig}}(\infty)$, where $\infty$ is the class of $(1,0)$, if and only if $f \cdot y = x$ for some Laurent series $x, y$ over $A$ with $y$ having nonzero coefficientwise reduction; (ii) every $\ell$ is $\mathrm{red}_q(\gamma) \cdot \infty$ for some $\gamma \in \Gamma_0(M')$ with $O^{\mathrm{Ig}}(\ell)$ the pullback of $O^{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`; (iii) $O^{\mathrm{Ig}}$ is injective; (iv) for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pullbacks along `levelAutBar q M' ζ' γ` permute the family $O^{\mathrm{Ig}}$; (v) for each $s$, an element of $\overline{\mathbb{Q}}$ lies in $O^{\mathrm{SS}}(s)$ exactly when it lies in $A$; (vi) for $f$ in the integers of $R_0$ which is nonnegative at every place where the base-changed $j$-expansion `jq` is nonnegative and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathcal{F}$ lies in $O^{\mathrm{SS}}(s)$, and for every $a \in A$ whose residue is the value at $s$ of that $R_0$-residue, the difference of the image of $f$ and $a$ lies in the maximal ideal of $O^{\mathrm{SS}}(s)$; (vii) each $O^{\mathrm{SS}}(s)$ is invariant under pullback along `levelAutBar q M' ζ' γ` for $\gamma \in \Gamma_0(M')$; (viii) each $O^{\mathrm{SS}}(s)$ contains an element $t$ with $t - a$ a unit of $O^{\mathrm{SS}}(s)$ for every $a \in A$. Finally let $R$ be a regular prolongation of $A$ from $\mathcal{F}$ to `xHFunctionFieldC κ (q^2*M') (levelH q M')` whose integers are $O^{\mathrm{Ig}}(\infty)$, and assume membership in the integers of $R_0$ is equivalent to membership of the image in $O^{\mathrm{Ig}}(\infty)$. The conclusion asserts the existence of a finite set $N^{\mathrm{Ig}}$ of places of $\kappa$ in `xHFunctionFieldC κ (q^2*M') (levelH q M')` with $|N^{\mathrm{Ig}}| = |W|$, together with a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to that field such that, first, for every $f$ in the integers of $R_0$ the image of $f$ in $\mathcal{F}$ lies in the integers of $R$ and its $R$-residue is $j$ applied to its $R_0$-residue, and second, $Q \in N^{\mathrm{Ig}}$ if and only if there is $s \in W$ with $g$ in the valuation subring of $s$ exactly when $j(g)$ is in the valuation subring of $Q$, for all $g$ in `modularFunctionFieldC κ M'`.
--
--   The statement identifies the nodes on the $\infty$-component of the Igusa model: through the reduction $j$ of level-$M'$ functions induced by the regular prolongation whose integers are the Gauss ring at $\infty$, the places of the Igusa reduced field singled out are exactly those lying over the supersingular places $W$, one for each, reflecting total ramification of the Igusa curve over the supersingular points. It is used by [`ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks`](thm.html#ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks) and by [`ModularCurve.FullLevel.exists_stalk_etaleCoordinate_residueChar_of_offBranch_of_reads_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.exists_stalk_etaleCoordinate_residueChar_of_offBranch_of_reads_twoChartIntegralModel) in the construction of the semistable model at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing.lean

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

theorem ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing
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
    ∃ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),

      NIg.card = W.card ∧

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) := by sorry
