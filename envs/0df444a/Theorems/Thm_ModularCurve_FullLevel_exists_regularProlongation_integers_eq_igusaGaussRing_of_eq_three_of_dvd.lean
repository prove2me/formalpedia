-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/5378149c-1dd7-5aff-9354-3d2b5893493b
-- title:
--   Regular prolongation on the Igusa Gauss ring at q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number not divisible by $q$, and suppose some prime $\ell$ with $\ell\equiv 11\pmod{12}$ divides $M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$, and write $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places `ssPlaces q M' κ` (rational affine geometric places whose value on the geometric $j$-generator lies in `ssJSet q κ`). Assume the base-changed full-level field $\mathrm{modularFunctionFieldBar}\,M'$ sits inside $\mathrm{fieldBar}\,q\,M'=\mathrm{xHFunctionFieldBar}(q^2M',\mathrm{levelH}\,q\,M')$, where `levelH q M'` is the kernel of the unit reduction map `ZMod.unitsMap (dvd_sq_mul q M')`. Let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (a valuation subring `R₀.integers`, a surjective residue homomorphism with kernel the maximal ideal, lying over $A$ and compatible with its residue map, a scaling property, and a place map preserving degrees and divisor pushforward), and assume $R_0$ is coefficientwise: every Laurent series $y$ over $A$ whose image in $\overline{\mathbb{Q}}((t))$ lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in `R₀.integers` and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and let $O_{\mathrm{Ig}}$ be a family of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by the projective line over $\mathbb{Z}/q$, and $O_{\mathrm{SS}}$ one indexed by $W$, subject to: (i) $O_{\mathrm{Ig}}(\infty)$ is the Gauss ring, consisting of those $f$ for which there are Laurent series $x,y$ over $A$ with $y$ having nonzero coefficientwise reduction and $f\cdot y=x$ in $\overline{\mathbb{Q}}((t))$; (ii) every point of the projective line is $\mathrm{redQ}\,q\,\gamma\cdot\infty$ for some $\gamma\in\Gamma_0(M')$, and $O_{\mathrm{Ig}}$ at that point is the pullback of $O_{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; (iii) $O_{\mathrm{Ig}}$ is injective; (iv) for all $\zeta'$ and all $\gamma\in\Gamma_0(M')$, pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permutes the family $O_{\mathrm{Ig}}$; (v) each $O_{\mathrm{SS}}(s)$ lies over $A$, in the sense that a constant lies in it precisely when it lies in $A$; (vi) for $s\in W$ and $f$ in `R₀.integers` whose order is nonnegative at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the $j$-function has nonnegative order, and whose $R_0$-residue lies in the valuation subring of $s$: the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{SS}}(s)$, and for every $a\in A$ whose residue equals the value at $s$ of the $R_0$-residue of $f$, the difference $f-a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$; (vii) each $O_{\mathrm{SS}}(s)$ is invariant under pullback along all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma\in\Gamma_0(M')$; (viii) each $O_{\mathrm{SS}}(s)$ contains an element $t$ such that $t-a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a\in A$. Then there is a regular prolongation $R$ of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $\mathrm{xHFunctionFieldC}\,\kappa\,(q^2M')\,(\mathrm{levelH}\,q\,M')$ — a valuation subring with a surjective residue homomorphism onto that field whose kernel is the maximal ideal, lying over $A$ and compatible with its residue map, and such that every nonzero element becomes, after multiplication by a suitable constant, an integral element with nonzero residue — whose ring of integers is exactly $O_{\mathrm{Ig}}(\infty)$.
--
--   This is the charting step at the cusp $\infty$ in the assembly of a semistable covering of the modular curve $X(\Gamma_H(q^2M'))$ in the case $q=3$, where the auxiliary prime $\ell\equiv 11\pmod{12}$ dividing $M'$ rigidifies the supersingular points; it equips the Igusa-component Gauss ring with a regular prolongation whose reduction is the function field of the Igusa-level curve over the residue field. It is used by the theorem that assembles the semistable covering together with its equivalence clauses from the given families of valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
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

theorem ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_three_of_dvd
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
    :
    ∃ R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), R.integers = OIg (lineInfty q) := by sorry
