-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/33496631-b67e-52c9-80a8-496d10692814
-- title:
--   Regular prolongation with Igusa Gauss ring at ∞, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number not divisible by $q$, and suppose some prime $\ell$ with $\ell\equiv 11\pmod{12}$ divides $M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, and write $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places `ssPlaces q M' κ` (rational affine geometric places at which the generator $j$ evaluates into the supersingular $j$-set). Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ inside the Laurent series over $\overline{\mathbb Q}$, and let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ such that every Laurent series $y$ over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$ and has $R_0$-residue equal, as a Laurent series over $\kappa$, to the coefficientwise reduction of $y$. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb Q}$, and let $O_{\mathrm{Ig}}$ be a family of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by the projective line over $\mathbb Z/q$ and $O_{\mathrm{SS}}$ one indexed by $W$, subject to: the Gauss-ring presentation of $O_{\mathrm{Ig}}(\infty)$ (its elements are the $f$ with $f\cdot\bar y=\bar x$ for Laurent series $x,y$ over $A$ with $y$ having nonzero reduction); transitivity of the $\Gamma_0(M')$-action on the indices through the automorphisms $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ together with the corresponding description of each $O_{\mathrm{Ig}}(\ell)$ as a pullback of $O_{\mathrm{Ig}}(\infty)$; injectivity of $O_{\mathrm{Ig}}$; permutation of the $O_{\mathrm{Ig}}$ by all such automorphisms; for the supersingular rings, the conditions that $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ exactly in $A$, that $O_{\mathrm{SS}}(s)$ dominates $R_0$ at $s$ for functions regular wherever $j$ is (giving membership and, after subtracting a suitable $a\in A$, membership in the maximal ideal), that each $O_{\mathrm{SS}}(s)$ is invariant under all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma\in\Gamma_0(M')$, and that each $O_{\mathrm{SS}}(s)$ contains an element $t$ with $t-a$ a unit for every $a\in A$ (these hypotheses are summarised here in the order listed). Then there exists a regular prolongation $R$ of $A$ to $\mathrm{fieldBar}\,q\,M'$ with residue field $\mathrm{xHFunctionFieldC}\,\kappa\,(q^2M')\,(\mathrm{levelH}\,q\,M')$ — that is, a valuation subring of $\mathrm{fieldBar}\,q\,M'$ meeting $\overline{\mathbb Q}$ in $A$, with a surjective residue homomorphism onto that field whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero element becomes, after scaling by a constant, an integral element with nonzero residue — whose ring of integers is $O_{\mathrm{Ig}}(\infty)$.
--
--   This is the step that upgrades the Gauss ring at the cusp $\infty$ of the Igusa-level data to a regular prolongation of $A$ to the full-level function field $\mathrm{fieldBar}\,q\,M'$, with reduced field the function field of $X_H(q^2M')$ over the residue field of $A$, in the case $q=2$ with a guard prime $\ell\equiv 11\pmod{12}$ dividing $M'$. It feeds the assembly of the semistable covering of the full-level modular curve, being used by [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two_of_dvd
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
