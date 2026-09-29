-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/41f10287-46bb-5535-bdac-e199f415f078
-- title:
--   Cusp-free Drinfeld discs lie in the supersingular tube (q=3)
-- statement:
--   Fix a prime $q$ with $q = 3$, a nonzero natural number $M'$ not divisible by $q$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, let $W$ be a finset of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\;q\;M'$ (rational places, affine geometric, with $j$-value in the supersingular set), and suppose $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$. Further data: a constant reduction $R_0$ of $A$ on the base-changed full level-$M'$ field with values in the characteristic-$q$ function field, compatible with coefficientwise reduction of Laurent series over $A$ ($hR_0$); a primitive $q$-th root of unity $\zeta$; families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to the Igusa clauses (explicit description of the ring at $\mathrm{lineInfty}\,q$ as ratios of Laurent series over $A$ with nonzero reduction of the denominator, transitivity under $\mathrm{redQ}$ of $\Gamma_0(M')$ together with transport by $\mathrm{levelAutBar}$, injectivity, and permutation of the family by $\mathrm{levelAutBar}$) and the supersingular clauses (the constants of $O_{\mathrm{SS}}\,s$ are exactly $A$; functions in $R_0.\mathrm{integers}$ that are regular wherever $\hat{\jmath}$ is and whose residue lies in the valuation subring of $s$ lie in $O_{\mathrm{SS}}\,s$ and are congruent there to any lift of the value of that residue at $s$; invariance of $O_{\mathrm{SS}}\,s$ under all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; existence of $t \in O_{\mathrm{SS}}\,s$ with $t - a$ a unit for every $a \in A$) — these are summarised here. Finally fix $s \in W$, a field $F_{\mathrm{SS}}$ over $\mathrm{ResidueField}\,A$, a component chart $C_b$ of $A$ on $\mathrm{fieldBar}\,q\,M'$ with values in $F_{\mathrm{SS}}$ whose integers are $O_{\mathrm{SS}}\,s$, a family $xt$ of places of $F_{\mathrm{SS}}$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$, and maps $\mathrm{disc}$, $\mathrm{coord}$ forming a disc family for the regular prolongation underlying $C_b$ over the finite set $\mathrm{image}\,xt$: for each place $Q$ outside that set, $\mathrm{disc}\,Q$ is a residue disc with coordinate $\mathrm{coord}\,Q$, and discs attached to distinct such $Q$ are disjoint. Assume moreover that these discs are cusp-free: for $Q \notin \mathrm{range}\,xt$ and $P \in \mathrm{disc}\,Q$, the order of $\hat{\jmath}$ (the image of $\mathrm{coeffEmb}\,\overline{\mathbb{Q}}\,\mathrm{jq}$) at $P$ is nonnegative. The conclusion: for every $Q \notin \mathrm{range}\,xt$, every $P \in \mathrm{disc}\,Q$, every $f \in R_0.\mathrm{integers}$ with nonnegative order at every place where $\hat{\jmath}$ has nonnegative order, whose $R_0$-residue lies in the valuation subring of $s$, and every $a \in A$ whose residue equals the value at $s$ of that residue, the difference $P.\mathrm{evalAt}$ of the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ minus $a$ lies in $A$ and in the maximal ideal of $A$.
--
--   This is the step asserting that the Drinfeld residue discs of a supersingular component chart lie in the tube of the supersingular place $s$: every admissible level-$M'$ function takes at each place of such a disc a value congruent modulo the maximal ideal of $A$ to its value at $s$. It is the $q = 3$ form, with the rigidifying hypothesis that $M'$ be divisible by a prime $\ell \equiv 11 \pmod{12}$, and it feeds into the assembly of the semistable covering of the modular curve of level $\Gamma_H(q^2M')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd
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
