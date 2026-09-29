-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing
-- name    : ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/2623fd36-72f4-5d44-852e-1797d1c9894d
-- title:
--   Regular prolongation whose integers are the Igusa ring at ∞
-- statement:
--   Fix a prime $q \ge 5$, a nonzero natural number $M'$ not divisible by $q$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$; write $\kappa$ for the residue field of $A$. Let $W$ be a finite set of places of $\kappa$-modular function field `modularFunctionFieldC κ M'` whose members are exactly the supersingular places `ssPlaces q M' κ` (rational affine geometric places at which the generic $j$-invariant takes a supersingular value), let `modularFunctionFieldBar M'` (the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field) be contained in `fieldBar q M'`, the base change to $\overline{\mathbb{Q}}$ of the $X_H$ function field of level $q^2M'$ for $H$ the kernel of $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, and let $R_0$ be a constant reduction of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` (a valuation subring with a surjective residue map onto the target whose kernel is the maximal ideal, compatible with $A$, together with a degree- and order-preserving map on places) satisfying: every Laurent series over $A$ whose coefficientwise image lies in `modularFunctionFieldBar M'` lies in the integers of $R_0$, and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of that series. Fix a primitive $q$-th root of unity $\zeta$ and families $O_{\mathrm{Ig}}$ of valuation subrings of `fieldBar q M'` indexed by the projective line over $\mathbb{Z}/q$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to the following hypotheses, summarised here: $O_{\mathrm{Ig}}$ at the point $[1:0]$ is the Gauss-type ring consisting of the $f$ for which $f\,y = x$ for some Laurent series $x,y$ over $A$ with $y$ having nonzero coefficientwise reduction; each $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}([1:0])$ along an automorphism `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$ moving $[1:0]$ to $\ell$; $O_{\mathrm{Ig}}$ is injective; pullback along any `levelAutBar q M' ζ' γ`, $\gamma \in \Gamma_0(M')$, permutes the family $O_{\mathrm{Ig}}$; each $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb{Q}}$ exactly in $A$, is fixed by all such pullbacks, contains an element $t$ with $t - a$ a unit of $O_{\mathrm{SS}}(s)$ for every $a \in A$, and is compatible with $R_0$ in the sense that an element $f$ of the integers of $R_0$ that is regular at every place where the $j$-function is regular and whose $R_0$-residue lies in the valuation subring of $s$ has image in $O_{\mathrm{SS}}(s)$, with $f - a$ in the maximal ideal of $O_{\mathrm{SS}}(s)$ whenever the residue of $a \in A$ is the value at $s$ of the $R_0$-residue of $f$. The conclusion: there is a regular prolongation $R$ of $A$ to `fieldBar q M'` with reduced field `xHFunctionFieldC κ (q^2 * M') (levelH q M')`, that is, a valuation subring of `fieldBar q M'` meeting $\overline{\mathbb{Q}}$ exactly in $A$, equipped with a surjective residue homomorphism onto that field whose kernel is the maximal ideal and which extends reduction on $A$, and such that every nonzero element becomes, after scaling by a constant, an element of the valuation subring with nonzero residue, whose ring of integers equals $O_{\mathrm{Ig}}([1:0])$.
--
--   This identifies the Gauss ring at the cusp $\infty$ as the local chart of the stable model of the full-level modular curve whose reduced function field is the $X_H$-function field of level $q^2M'$ over the residue field, i.e. the Igusa component. It is a step in the assembly of the semistable covering of $X_{\Gamma_H(q^2M')}$, and is used by the descent lemmas that compare charts, identify maximal ideals of the Drinfeld ring and produce smooth opens of the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing.lean

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

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing
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
    :
    ∃ R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), R.integers = OIg (lineInfty q) := by sorry
