-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/09b3e790-cece-59f5-9441-e1da85ddde34
-- title:
--   Igusa Gauss ring at ∞ cuts out the level-M' reduction (q=2)
-- statement:
--   Fix a prime $q$ with $q=2$, a nonzero level $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ dividing $M'$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ consisting exactly of the supersingular places $\mathrm{ssPlaces}\,q\,M'$ (rational, affine geometric, with $\mathrm{jGeomGen}$-value in the supersingular $j$-set). Assume the inclusion $\mathrm{hle}$ of $F_0 = \mathrm{modularFunctionFieldBar}\,M'$ into $F = \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $A$ on $F_0$ with reduced field $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$, so $R_0$ consists of a valuation subring $R_0.\mathrm{integers}$ of $F_0$, a surjective residue map onto the reduced field with kernel the maximal ideal, compatibility with $A$ and with orders of places; assume moreover that every Laurent series $y$ over $A$ whose coefficientwise image lies in $F_0$ is $R_0$-integral with $R_0$-residue the coefficientwise residue of $y$. Further data: a primitive $q$-th root of unity $\zeta$, a family $\mathrm{OIg}$ of valuation subrings of $F$ indexed by the projective line over $\mathbb{Z}/q$, and a family $\mathrm{OSS}$ indexed by $W$. The hypotheses on these are: $\mathrm{OIg}(\infty)$ is the Gauss ring at $\infty$, i.e. consists of the quotients $x/y$ of coefficientwise images of Laurent series over $A$ with $y$ having nonzero coefficientwise residue; each $\mathrm{OIg}$ at a line is the pullback of $\mathrm{OIg}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma \in \Gamma_0(M')$ moving $\infty$ to that line; $\mathrm{OIg}$ is injective and the family is permuted by pullback along all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; each $\mathrm{OSS}(s)$ meets $\overline{\mathbb{Q}}$ in $A$, is invariant under these same pullbacks, contains an element $t$ with $t - a$ a unit for every $a \in A$, and receives each $R_0$-integral $f$ that is regular wherever the $j$-function expansion is regular and whose $R_0$-residue is $s$-integral, with $f - a$ in the maximal ideal of $\mathrm{OSS}(s)$ whenever the residue of $a \in A$ is the $s$-value of that $R_0$-residue. The conclusion: for every $f \in F_0$, $f$ lies in $R_0.\mathrm{integers}$ if and only if its image in $F$ lies in $\mathrm{OIg}(\mathrm{lineInfty}\,q)$.
--
--   This identifies the abstractly given constant reduction $R_0$ of the level-$M'$ modular function field with the restriction to that field of the Igusa Gauss valuation ring at the cusp $\infty$ of the full-level field, a $q$-expansion principle in valuation-theoretic form; it is the $q=2$ case, with the auxiliary rigidifying prime $\ell \equiv 11 \pmod{12}$ dividing $M'$. It feeds the construction of the semistable covering of the full-level curve by Igusa and supersingular charts over $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd
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
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s)) :
    ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q) := by sorry
