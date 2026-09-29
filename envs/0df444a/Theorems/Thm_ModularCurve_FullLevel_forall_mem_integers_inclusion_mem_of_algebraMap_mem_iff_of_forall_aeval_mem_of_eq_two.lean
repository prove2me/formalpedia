-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem_of_eq_two
-- name    : ModularCurve.FullLevel.forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/22990e0f-432a-5a15-a2cf-2ac11a7e0e13
-- title:
--   Level-M' reduction integers lie in every j-adapted ring (q=2)
-- statement:
--   Fix a prime $q$ with $q = 2$, a natural number $M' \neq 0$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over $\mathrm{ResidueField}\,A$ consisting exactly of the supersingular places for $q$ (rational places, affine geometric, whose value at the geometric $j$ lies in the supersingular $j$-set). Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ inside the Laurent series field over $\overline{\mathbb Q}$, and let $R_0$ be a `ConstantReduction` of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with residue field target $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$, pinned coefficientwise by $hR_0$: every Laurent series $y$ over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\mathrm{ResidueField}\,A$, is the coefficientwise reduction of $y$. Further data: a primitive $q$-th root of unity $\zeta$, a family $O^{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb Z/q)$, and a family $O^{\mathrm{SS}}$ indexed by $W$, subject to hypotheses summarised as: $O^{\mathrm{Ig}}$ at the line $\infty$ consists of the quotients $x/y$ of Laurent series over $A$ with $y$ of nonzero reduction; every index is reached from $\infty$ by some $\gamma \in \Gamma_0(M')$ via $\mathrm{redQ}$ and pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; $O^{\mathrm{Ig}}$ is injective and permuted by all such pullbacks; each $O^{\mathrm{SS}}_s$ meets $\overline{\mathbb Q}$ exactly in $A$, is fixed by those pullbacks, contains an element $t$ with $t - a$ a unit for all $a \in A$, and is compatible with $R_0$ and $s$ in the sense that an $f \in R_0.\mathrm{integers}$ with non-negative order wherever $j$ has non-negative order and with $R_0$-residue in the valuation ring of $s$ maps into $O^{\mathrm{SS}}_s$, congruent modulo the maximal ideal to any $a \in A$ whose residue is the value of that residue at $s$. Finally let $O$ be a valuation subring of $\mathrm{fieldBar}\,q\,M'$ with $O \cap \overline{\mathbb Q} = A$ and such that for every polynomial $P$ over $A$ with nonzero reduction both $P(j)$ and $P(j)^{-1}$ lie in $O$, where $j$ is the image of the base-changed $q$-expansion $\mathrm{jq}$. The conclusion: every $f \in \mathrm{modularFunctionFieldBar}\,M'$ lying in $R_0.\mathrm{integers}$ has its image under the inclusion into $\mathrm{fieldBar}\,q\,M'$ in $O$.
--
--   This is the containment step in the identification of the valuation rings of the full-level field above a valuation ring $A$ of $\overline{\mathbb Q}$ over $q$: any ring adapted to $j$ in the stated sense dominates the good-reduction ring of the level-$M'$ floor. It is the $q = 2$ case, and is used by [`ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two) on the Igusa leg of the semistable-covering construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem_of_eq_two.lean

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

theorem ModularCurve.FullLevel.forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem_of_eq_two
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

    (O : ValuationSubring (fieldBar q M'))
    (hOA : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A)
    (hOj : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') P ∈ O ∧
      (Polynomial.aeval (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') P)⁻¹ ∈ O) :
    ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers → (IntermediateField.inclusion hle f : fieldBar q M') ∈ O := by sorry
