-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/7cc63d96-9530-5eda-be56-f6ee78afad06
-- title:
--   Constant reduction integers equal the Igusa Gauss ring at ∞ (q=3)
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\equiv 11 \pmod{12}$ and $\ell\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, i.e. with $q$ a non-unit of $A$, and write $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places for $q$ (rational places, affine geometric, whose value at the geometric $j$-generator lies in the supersingular $j$-set), let $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ be the inclusion `hle` of the $\overline{\mathbb Q}$-base-changed level-$M'$ full modular function field into the function field of $X_H$ of level $q^2M'$ with $H$ the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$, and let $R_0$ be a constant reduction of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with reduced field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$, assumed ($hR_0$) to satisfy: every Laurent series $y$ over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Fix a primitive $q$-th root of unity $\zeta$, and families $O^{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb Z/q)$ and $O^{\mathrm{SS}}$ indexed by $W$, subject to: $f\in O^{\mathrm{Ig}}(\infty)$ exactly when $f\cdot y=x$ for Laurent series $x,y$ over $A$ with $y$ having nonzero reduction; each $O^{\mathrm{Ig}}(\lambda)$ is the pullback of $O^{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma\in\Gamma_0(M')$ carrying $\infty$ to $\lambda$ under reduction mod $q$; $O^{\mathrm{Ig}}$ is injective and the pullbacks along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$, $\gamma\in\Gamma_0(M')$, permute the family; each $O^{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ in exactly $A$, is fixed by all these pullbacks, contains an element $t$ with $t-a$ a unit for every $a\in A$, and satisfies a compatibility ($hSS_{\mathrm{over}}$): for $f$ in $R_0$'s integers whose order is nonnegative at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the image of $j_q$ has nonnegative order, and whose $R_0$-residue lies in the valuation ring of $s$, the image of $f$ lies in $O^{\mathrm{SS}}(s)$, and for $a\in A$ whose residue is the value of the $R_0$-residue of $f$ at $s$, the image of $f$ minus $a$ lies in the maximal ideal of $O^{\mathrm{SS}}(s)$. Then for every $f$ in $\mathrm{modularFunctionFieldBar}\,M'$: $f$ lies in the valuation subring $R_0.\mathrm{integers}$ if and only if its image in $\mathrm{fieldBar}\,q\,M'$ lies in $O^{\mathrm{Ig}}(\infty)$.
--
--   This is the $q$-expansion form of the comparison between the level-$M'$ Gauss (constant) reduction at a place over $3$ and the Igusa Gauss valuation ring at the cusp $\infty$ of the full level $q^2M'$ curve, with the auxiliary level divisor $\ell\equiv 11\pmod{12}$ serving as a rigidity guard in characteristic $3$. It is used in the construction of the semistable covering data for $X_H$ at $q=3$, by [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_three_of_dvd
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
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s)) :
    ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q) := by sorry
