-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/5f7aeabd-b3fe-570f-8339-114446286e93
-- title:
--   Drinfeld residue discs lie in the supersingular tube, q=2
-- statement:
--   Fix a prime $q$ with $q=2$, a nonzero level $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ whose members are exactly the supersingular places `ssPlaces q M'` (rational places, affine geometric, whose value at the geometric $j$-generator lies in the supersingular $j$-set), and assume the base-changed full-level field $\mathrm{modularFunctionFieldBar}\,M'$ is contained in $\mathrm{fieldBar}\,q\,M'$ via `hle`. Further data: a constant reduction $R_0$ of $\mathrm{modularFunctionFieldBar}\,M'$ over $A$ with residue target $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A,M')$ (a valuation subring with a surjective residue map whose kernel is the maximal ideal, contracting to $A$, together with a degree- and divisor-compatible map of places), whose residue on Laurent series with coefficients in $A$ is coefficientwise reduction (`hR₀`); an index $\zeta$ of primitive $q$-th roots of unity; a family $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb F_q)$, the one at `lineInfty q` being described by existence of a quotient representation with reduction-nonzero denominator, the others being its pullbacks along $\mathrm{levelAutBar}$ of elements of $\Gamma_0(M')$, with $O_{\mathrm{Ig}}$ injective and permuted by those automorphisms; and a family $O_{\mathrm{SS}}$ of valuation subrings indexed by $W$, contracting to $A$ on $\overline{\mathbb Q}$, invariant under all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$, containing a parameter $t$ such that $t - a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a \in A$, and satisfying the clause `hSS_over`: every $f$ in the integers of $R_0$ whose order is nonnegative at each place where $\hat\jmath = \mathrm{coeffEmb}\,\overline{\mathbb Q}\,\mathrm{jq}$ has nonnegative order and whose $R_0$-residue lies in the valuation subring of $s$, lies in $O_{\mathrm{SS}}(s)$, and for each $a \in A$ reducing to the value of that residue at $s$, $f - a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$. Fix $s \in W$, a field $F_{\mathrm{SS}}$ over $\mathrm{ResidueField}\,A$, a component chart $C_b$ over $A$ for $\mathrm{fieldBar}\,q\,M'$ with values in $F_{\mathrm{SS}}$ whose integers are $O_{\mathrm{SS}}(s)$, attachment directions $x_t : \mathbb P^1(\mathbb F_q) \to$ places of $F_{\mathrm{SS}}$, and maps $\mathrm{disc}$, $\mathrm{coord}$ such that the regular prolongation underlying $C_b$ admits these as a disc family over the complement of the image of $x_t$ (each such $Q$ has $\mathrm{disc}\,Q$ a residue disc with coordinate $\mathrm{coord}\,Q$, and distinct such $Q$ have disjoint discs). Assume moreover that $\hat\jmath$ has nonnegative order at every place of every disc $\mathrm{disc}\,Q$ with $Q$ outside the image of $x_t$. The conclusion: for every such $Q$, every $P \in \mathrm{disc}\,Q$, every $f$ in the integers of $R_0$ whose order is nonnegative wherever $\hat\jmath$'s is and whose $R_0$-residue lies in the valuation subring of $s$, and every $a \in A$ whose reduction equals the value of that residue at $s$, the value $P.\mathrm{evalAt}$ of the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ minus $a$ lies in $A$ and in the maximal ideal of $A$.
--
--   This is the cusp-free case of the statement that the Drinfeld residue discs of a supersingular component chart lie in the tube of the corresponding supersingular place: on such a disc every admissible level-$M'$ function takes a value congruent, modulo the maximal ideal of $A$, to its value at the supersingular place $s$. It is the $q = 2$ form, with the auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing the tame level, of a step used in assembling the semistable covering of the full-level modular curve, and it is cited by [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_two_of_dvd
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
