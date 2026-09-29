-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularChart_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularChart_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/c1b1c885-c4da-53d6-9786-ec6a11ba1c14
-- title:
--   Existence and uniqueness of the supersingular chart at q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ with $q$ a non-unit of $A$, and write $\kappa = \mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of the field $\mathrm{modularFunctionFieldC}\,\kappa\,M' = \kappa(j_q, j_q^{(M')})$ over $\kappa$ consisting exactly of the supersingular places, i.e. the rational places lying on the affine geometric part whose value of the geometric $j$-generator lies in the supersingular $j$-set in characteristic $q$. Assume $\mathrm{modularFunctionFieldBar}\,M'$, the $\overline{\mathbb Q}$-base change of the full level-$M'$ modular function field inside $\overline{\mathbb Q}((q))$, is contained in $\mathrm{fieldBar}\,q\,M'$, the $\overline{\mathbb Q}$-base change of the function field of $X_H$ of level $q^2M'$ with $H$ the kernel of $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$. Let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with residue field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (a valuation subring with surjective residue map whose kernel is the maximal ideal, inducing the residue map of $A$ on constants, satisfying the scaling axiom, and with a degree-preserving place map compatible with divisor pushforward), and assume $R_0$ is pinned coefficientwise: every Laurent series with coefficients in $A$ whose image in $\overline{\mathbb Q}((q))$ lies in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral, with $R_0$-residue the coefficientwise reduction of that series. Then for each $s \in W$ there are a field $\mathrm{FSS}$ that is a $\kappa$-algebra and a component chart $C$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ with residue field $\mathrm{FSS}$ (a valuation subring, a surjective residue map with kernel the maximal ideal extending the residue map of $A$, a domain of places, a finite set of nodes, and a place map satisfying the pointwise and divisor-pushforward compatibilities) such that: $\mathrm{FSS}$ contains an element transcendental over $\kappa$; for every $R_0$-integral $f \in \mathrm{modularFunctionFieldBar}\,M'$ whose order is non-negative at every place of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which the $q$-expansion $j_q$ of $j$ has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ is $C$-integral with $C$-residue the image in $\mathrm{FSS}$ of the value at $s$ of the $R_0$-residue of $f$; the valuation subring of $C$ is preserved by pullback along the level automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for every primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb Q}$ and every $\gamma \in \Gamma_0(M')$; and any component chart $C'$ over any $\kappa$-algebra field $F'$ with these three properties has the same valuation subring as $C$.
--
--   This is the supersingular (Drinfeld) chart of the semistable reduction of the full-level modular curve in residue characteristic $2$, cut out at a chosen supersingular place $s$ and characterised intrinsically by its behaviour on level-$M'$ functions regular where $j$ is and by $\Gamma_0(M')$-invariance; the auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing $M'$ rigidifies the supersingular points. It feeds the construction of the semistable covering of the full-level curve at $q = 2$ used in the descent and inertia-at-infinity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularChart_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_supersingularChart_of_eq_two_of_dvd
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
    (s : ↥W) :
    ∃ (FSS : Type) (_ : Field FSS) (_ : Algebra (ResidueField A) FSS)
      (C : ComponentChart A (fieldBar q M') FSS),

      (∃ t : FSS, Transcendental (ResidueField A) t) ∧

      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers,
            C.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        (C.comap (levelAutBar q M' ζ γ)).integers = C.integers) ∧

      (∀ (F' : Type) [Field F'] [Algebra (ResidueField A) F'] (C' : ComponentChart A (fieldBar q M') F'),
        (∃ t : F', Transcendental (ResidueField A) t) →
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C'.integers,
              C'.residue ⟨_, hC⟩ = algebraMap (ResidueField A) F'
                ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                  (R₀.residue ⟨f, hf⟩))) →
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
          (C'.comap (levelAutBar q M' ζ γ)).integers = C'.integers) →
        C'.integers = C.integers) := by sorry
