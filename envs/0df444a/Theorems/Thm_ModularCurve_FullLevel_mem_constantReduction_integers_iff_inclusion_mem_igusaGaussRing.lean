-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing
-- name    : ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/1d1ab50f-8222-53e6-a377-ad7731df7fd2
-- title:
--   Level-M' reduction integers are the Igusa Gauss ring at ∞
-- statement:
--   Let $q\ge 5$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and $A$ a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over the residue field of $A$ whose members are exactly the supersingular places (rational, affine geometric, with supersingular $j$-value). Assume the base-changed level-$M'$ field $\mathrm{modularFunctionFieldBar}\,M'$ is contained in $\mathrm{fieldBar}\,q\,M'$ inside $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$, and let $R_0$ be a constant reduction of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with reduced field $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$, such that every Laurent series $y$ with coefficients in $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral with $R_0$-residue the coefficientwise reduction of $y$. Fix a primitive $q$-th root of unity $\zeta$ and families $O^{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and $O^{\mathrm{SS}}$ indexed by $W$, subject to: $O^{\mathrm{Ig}}(\infty)$ consists exactly of the quotients $x/y$ of Laurent series with coefficients in $A$ whose denominator has nonzero coefficientwise reduction; the other $O^{\mathrm{Ig}}(\ell)$ are the pullbacks of $O^{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for suitable $\gamma\in\Gamma_0(M')$, with $O^{\mathrm{Ig}}$ injective and permuted by all such pullbacks; and four conditions on the supersingular rings $O^{\mathrm{SS}}$ (trace on $\overline{\mathbb{Q}}$ equal to $A$, compatibility of $R_0$-integral elements having nonnegative order wherever $j$ does with reduction at places of $W$, invariance under the automorphisms $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma\in\Gamma_0(M')$, and existence of an element of $O^{\mathrm{SS}}(s)$ differing from every element of $A$ by a unit), summarised here. Then for every $f$ in $\mathrm{modularFunctionFieldBar}\,M'$, $f$ lies in the valuation subring $R_0.\mathrm{integers}$ if and only if its image in $\mathrm{fieldBar}\,q\,M'$ lies in $O^{\mathrm{Ig}}(\infty)$.
--
--   The statement identifies the abstractly given constant reduction of the level-$M'$ modular function field with the restriction of the Gauss valuation ring at the cusp $\infty$ of the full-level field, a $q$-expansion principle in valuation-theoretic form. It is used in the descent arguments producing charts and places of the semistable integral model at level $q^2M'$, for instance in [`ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent`](thm.html#ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing
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
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s)) :
    ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q) := by sorry
