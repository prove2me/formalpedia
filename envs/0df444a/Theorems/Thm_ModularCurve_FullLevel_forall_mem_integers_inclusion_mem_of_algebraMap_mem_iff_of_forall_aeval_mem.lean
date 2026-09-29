-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem
-- name    : ModularCurve.FullLevel.forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/683d9721-0ce7-5839-87df-9ce76e6e5387
-- title:
--   Good-reduction integers of the level-M' floor lie in O
-- statement:
--   Fix a prime $q \ge 5$, a nonzero natural number $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ belongs to the non-units of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ (\mathrm{ResidueField}\ A)\ M'$ over $\mathrm{ResidueField}\ A$ whose members are exactly the supersingular places, i.e. those rational affine geometric places at which the value of the geometric $j$-generator lies in the supersingular $j$-set for $q$. Let $\mathrm{hle}$ be the inclusion of $\mathrm{modularFunctionFieldBar}\ M'$, the base change to $\overline{\mathbb Q}$ of the full level-$M'$ function field, into $\mathrm{fieldBar}\ q\ M'$, the base change of the $X_H$-function field at level $q^2M'$ with $H$ the kernel of reduction to level $q$. Let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\ M'$ along $A$ with residue field target $\mathrm{modularFunctionFieldC}\ (\mathrm{ResidueField}\ A)\ M'$ — so a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism with kernel its maximal ideal, compatible with $A$ and with orders of places — pinned coefficientwise by the hypothesis that every Laurent series $y$ over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\ M'$ lies in $R_0.\mathrm{integers}$ with $R_0$-residue the coefficientwise reduction of $y$. Further data are summarised in three groups: a primitive $q$-th root of unity index $\zeta$; an Igusa family $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\ q\ M'$ indexed by the projective line over $\mathbb Z/q$, subject to the description of $O_{\mathrm{Ig}}(\infty)$ as the set of quotients of Laurent series over $A$ with denominator of nonzero reduction, to transitivity of the $\Gamma_0(M')$-automorphisms $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$ on the family, to injectivity, and to the requirement that pullback along $\mathrm{levelAutBar}\ q\ M'\ \zeta'\ \gamma$ permutes the family; and a supersingular family $O_{\mathrm{SS}}$ indexed by $W$, each meeting $\overline{\mathbb Q}$ exactly in $A$, invariant under all these automorphisms, admitting for each $s$ an element $t$ of $O_{\mathrm{SS}}(s)$ with all differences $t-a$ ($a \in A$) units, and such that for $f \in R_0.\mathrm{integers}$ which is regular at every place where $j$ is regular and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ lies in $O_{\mathrm{SS}}(s)$ and is congruent modulo the maximal ideal to any $a \in A$ whose residue is the value of the residue of $f$ at $s$. Finally let $O$ be a valuation subring of $\mathrm{fieldBar}\ q\ M'$ with $O \cap \overline{\mathbb Q} = A$ and such that for every polynomial $P$ over $A$ with nonzero reduction, $P$ evaluated at the image of $j$ lies in $O$ together with its inverse. The conclusion is that every $f \in R_0.\mathrm{integers}$ has image in $O$ under the inclusion of $\mathrm{modularFunctionFieldBar}\ M'$ into $\mathrm{fieldBar}\ q\ M'$.
--
--   This is the uniqueness of the prolongation to the level-$M'$ floor of the Gauss valuation of $\overline{\mathbb Q}(j)$ determined by $A$: good reduction of $X_0(M')$ at a prime $q$ not dividing $M'$ forces the intersection of $O$ with the floor to contain the good-reduction ring $R_0.\mathrm{integers}$. It supplies the corresponding hypothesis in [`ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField`](thm.html#ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField), which identifies valuation subrings of the level field with the Igusa and supersingular charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open ModularCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem
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

    (O : ValuationSubring (fieldBar q M'))
    (hOA : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A)
    (hOj : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') P ∈ O ∧
      (Polynomial.aeval (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') P)⁻¹ ∈ O) :
    ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers → (IntermediateField.inclusion hle f : fieldBar q M') ∈ O := by sorry
