-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_arithmeticGalois_smul_mem_drinfeldRing_iff_of_componentChart_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.arithmeticGalois_smul_mem_drinfeldRing_iff_of_componentChart_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/4e4efc7b-9362-5a15-a9d3-a7f2719a2d12
-- title:
--   Inertia fixes the supersingular Drinfeld rings, q=3
-- statement:
--   Fix a prime $q$ with $q=3$ and a nonzero $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular set for $q$). Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ inside $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A,M')$ (a valuation subring of the source, a surjective residue map with kernel the maximal ideal, and a place map of the stated degree and divisor compatibilities), whose integers contain every Laurent series with coefficients in $A$ lying in $\mathrm{modularFunctionFieldBar}\,M'$, with residue the coefficientwise reduction. Let $\zeta$ be a primitive $q$-th root of unity, $O_{\mathrm{Ig}}$ a family of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and $O_{\mathrm{SS}}$ one indexed by $W$. The hypotheses on $O_{\mathrm{Ig}}$ (description at $\infty$ as ratios of series with $A$-coefficients and nonzero reduced denominator, transitivity under $\mathrm{levelAutBar}$ for $\gamma \in \Gamma_0(M')$, injectivity, permutation of the family under pullback) and on $O_{\mathrm{SS}}$ (meeting $\overline{\mathbb{Q}}$ exactly in $A$; lying over $s$ for $j$-regular elements of $R_0$'s integers, with the prescribed congruence against $A$; invariance under pullback along every $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; existence of a transcendental $t$ with all $t-a$, $a \in A$, units) are summarised here. Each $O_{\mathrm{SS}}(s)$ is realised as the ring of integers of a component chart $\mathrm{CSS}(s)$ with residue field $\mathrm{FSS}(s)$, a curve over $\mathrm{ResidueField}\,A$ essentially of finite type; finally $\pi \in A$ satisfies $\pi^{q^2-1} = q$. The conclusion: for every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$, every $s \in W$ and every $f$ in $\mathrm{fieldBar}\,q\,M'$, the coefficientwise image of $f$ under $\mathrm{arithmeticGalois}$ applied to $\tau$ lies in $O_{\mathrm{SS}}(s)$ if and only if $f$ does.
--
--   This is the inertia-invariance step for the supersingular (type II) charts in the semistable covering of the modular curve of level $\Gamma_H(q^2M')$, in the case $q=3$, where the rigidifying prime $\ell \equiv 11 \pmod{12}$ dividing $M'$ compensates for the extra automorphisms of the supersingular $j$-invariant in characteristic $3$. It feeds the naturality statement for inertia on the supersingular charts of that covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_arithmeticGalois_smul_mem_drinfeldRing_iff_of_componentChart_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.arithmeticGalois_smul_mem_drinfeldRing_iff_of_componentChart_of_eq_three_of_dvd
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

    (FSS : ↥W → Type) [∀ s, Field (FSS s)] [∀ s, Algebra (ResidueField A) (FSS s)]
    [∀ s, IsCurveOver (ResidueField A) (FSS s)] [∀ s, Algebra.EssFiniteType (ResidueField A) (FSS s)]
    (CSS : ∀ s : ↥W, ComponentChart A (fieldBar q M') (FSS s)) (hCSS : ∀ s, (CSS s).integers = OSS s)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ (s : ↥W) (f : fieldBar q M'),
      ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ OSS s ↔ f ∈ OSS s := by sorry
