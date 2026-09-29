-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree
-- name    : ModularCurve.FullLevel.inTube_of_mem_drinfeldDisc_of_cuspFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/7b0264c4-4c64-538a-993a-f23cb5277714
-- title:
--   Cusp-free residue discs lie in the supersingular tube
-- statement:
--   Let $q \ge 5$ be a prime, $M'$ a nonzero natural number not divisible by $q$, and $A$ a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ (\mathrm{ResidueField}\ A)\ M'$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\ q\ M'$ (rational affine geometric places at which the geometric $j$-invariant takes a supersingular value), let $\mathrm{modularFunctionFieldBar}\ M' \le \mathrm{fieldBar}\ q\ M'$ inside the Laurent series over $\overline{\mathbb{Q}}$, and let $R_0$ be a constant reduction of the level-$M'$ field with residue field the level-$M'$ function field over $\mathrm{ResidueField}\ A$, compatible with coefficientwise reduction of Laurent series with coefficients in $A$ ($hR_0$). Further data: a primitive $q$-th root of unity index $\zeta$, a family $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\ q\ M'$ indexed by $\mathbb{P}^1(\mathbb{F}_q)$ and a family $O_{\mathrm{SS}}$ indexed by $W$, subject to hypotheses summarised as follows: $O_{\mathrm{Ig}}$ at the point at infinity consists of the quotients of coefficientwise images of Laurent series over $A$ with nonzero reduced denominator, the remaining members are pullbacks along the automorphisms $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$ for $\gamma \in \Gamma_0(M')$ carrying the point at infinity to the given point, the family is injective and permuted by all such pullbacks; each $O_{\mathrm{SS}}\ s$ meets $\overline{\mathbb{Q}}$ exactly in $A$, is invariant under those pullbacks, admits an element $t$ with $t - a$ a unit for every $a \in A$, and satisfies the congruence clause $hSS_{\mathrm{over}}$: for $f$ in the integers of $R_0$ that is regular wherever $\hat{\jmath} = \mathrm{coeffEmb}\ \mathrm{jq}$ is, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ lies in $O_{\mathrm{SS}}\ s$ and differs from any $a \in A$ reducing to the value of that residue at $s$ by an element of the maximal ideal of $O_{\mathrm{SS}}\ s$. Fix $s \in W$, a field $F_{\mathrm{SS}}$ over $\mathrm{ResidueField}\ A$, a component chart $C_b$ for $A$ and $\mathrm{fieldBar}\ q\ M'$ with values in $F_{\mathrm{SS}}$ whose integers are $O_{\mathrm{SS}}\ s$, a map $xt$ from $\mathbb{P}^1(\mathbb{F}_q)$ to places of $F_{\mathrm{SS}}$, and maps $\mathrm{disc}$, $\mathrm{coord}$ forming a residue-disc family for the regular prolongation underlying $C_b$ outside the image of $xt$ (each such disc is a residue disc with coordinate $\mathrm{coord}\ Q$, and discs at distinct such places are disjoint), with $\hat{\jmath}$ of nonnegative order at every place of every such disc. The conclusion: for every place $Q$ outside the range of $xt$, every $P \in \mathrm{disc}\ Q$, every $f$ in the integers of $R_0$ regular wherever $\hat{\jmath}$ is and with $R_0$-residue in the valuation subring of $s$, and every $a \in A$ whose residue is the value of that $R_0$-residue at $s$, the value $P.\mathrm{evalAt}$ of the image of $f$ in $\mathrm{fieldBar}\ q\ M'$ minus $a$ lies in $A$ and in the maximal ideal of $A$.
--
--   This is the statement that the Drinfeld residue discs of a component chart over a supersingular place $s$, on which $\hat{\jmath}$ has no pole, lie in the tube of $s$: every admissible level-$M'$ function takes at each place of such a disc a value congruent, modulo the maximal ideal of $A$, to its value at $s$. It is a step in the assembly of the semistable covering of the full-level modular curve, used by [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree.lean

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
open scoped Classical in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.inTube_of_mem_drinfeldDisc_of_cuspFree
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
    (s : ↥W) {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (Cb : ComponentChart A (fieldBar q M') FSS) (hCb : Cb.integers = OSS s)
    (xt : CuspidalType.ProjLine q → Place (ResidueField A) FSS)
    (disc : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M'))) (coord : Place (ResidueField A) FSS → (fieldBar q M'))
    (hfam : haveI := Fintype.ofFinite (CuspidalType.ProjLine q);
      (⟨Cb.integers, Cb.residue, Cb.algebraMap_mem_iff, Cb.residue_surjective, Cb.ker_residue, Cb.residue_algebraMap,
        Cb.exists_smul_mem⟩ : RegularProlongation A ↥(fieldBar q M') FSS).DiscFamily (Finset.univ.image xt) disc coord)

    (hcusp : ∀ Q : Place (ResidueField A) FSS, Q ∉ Set.range xt → ∀ P ∈ disc Q,
        0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M')) :
    ∀ Q, Q ∉ Set.range xt → ∀ P ∈ disc Q, (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A) := by sorry
