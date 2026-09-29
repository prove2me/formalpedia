-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_fullLevelFunction_residue_zero_unit_igusa_ord_zero_tubeAnnulus_jE_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_fullLevelFunction_residue_zero_unit_igusa_ord_zero_tubeAnnulus_jE_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/726421b1-c4bc-5f8a-9011-c42a36d890cc
-- title:
--   Full-level test function at q=2: Igusa unit, zero residue
-- statement:
--   Throughout, $q$ is a prime with $q = 2$, $M'$ is a nonzero natural number not divisible by $q$, and $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a nonunit of $A$; $W$ is a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over the residue field of $A$ whose members are, by `hW`, exactly the supersingular places `ssPlaces q M' (ResidueField A)`, that is the rational affine-geometric places at which the geometric $j$-coordinate `jGeomGen` takes a value in `ssJSet q`. The hypothesis `hle` asserts the inclusion $\overline{F}_{M'} := \mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ of intermediate fields of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ over $\overline{\mathbb Q}$, where $\overline{F}_{M'}$ is the $\overline{\mathbb Q}$-base change of the full level-$M'$ modular function field and $\mathrm{fieldBar}\,q\,M' = \mathrm{xHFunctionFieldBar}(q^2M', \mathrm{levelH}\,q\,M')$ is the function field over $\overline{\mathbb Q}$ of the curve $X_H$ of level $q^2M'$ for $H = \ker\bigl((\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times\bigr)$, the units congruent to $1$ modulo $q$. Write $\hat\jmath$ for the element of $\overline{F}_{M'}$ given by the coefficientwise image of the rational $j$-series `jq`, and also for its image in $\mathrm{fieldBar}\,q\,M'$ under `hle`.
--
--   The datum $R_0$ is a `ConstantReduction` of $\overline{F}_{M'}$ towards $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ relative to $A$: a valuation subring $R_0.\mathrm{integers}$ of $\overline{F}_{M'}$, a ring homomorphism $R_0.\mathrm{residue}$ from it onto the target with kernel the maximal ideal, a map on places preserving degrees and compatible with divisor push-forward, together with the requirements that a constant of $\overline{\mathbb Q}$ be integral exactly when it lies in $A$, that constants reduce to their residues in $\mathrm{ResidueField}\,A$, and that every nonzero element become integral with nonzero reduction after scaling by a constant. The hypothesis `hR₀` is the Gauss-reduction property: for every Laurent series $y$ over $A$ whose coefficientwise image in $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ lies in $\overline{F}_{M'}$, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\mathrm{ResidueField}\,A$, is the coefficientwise reduction of $y$.
--
--   Next, $\zeta$ is an element of $\mathrm{Idx}\,q$, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$, and two families of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ are given: $O^{\mathrm{Ig}}$ indexed by the projective line $\mathbb P^1(\mathbb Z/q)$ and $O^{\mathrm{SS}}$ indexed by $W$. Four hypotheses govern $O^{\mathrm{Ig}}$: `hIg_inf` says that $f$ lies in $O^{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ exactly when there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot y = x$ in $\mathrm{LaurentSeries}(\overline{\mathbb Q})$; `hIg` says that every line is of the form $\mathrm{redQ}\,q\,\gamma \cdot \mathrm{lineInfty}\,q$ for some $\gamma \in \Gamma_0(M')$ with $O^{\mathrm{Ig}}$ at that line equal to the preimage of $O^{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ under $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; `hIg_inj` says $O^{\mathrm{Ig}}$ is injective; and `hIg_perm` says that for every $\zeta' \in \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M')$ the maps $O^{\mathrm{Ig}}(\cdot)$ are permuted among themselves by taking preimages along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$.
--
--   Three hypotheses govern $O^{\mathrm{SS}}$. `hSS_A` says that a constant of $\overline{\mathbb Q}$ lies in $O^{\mathrm{SS}}(s)$ exactly when it lies in $A$. `hSS_over` says that for $s \in W$ and $f \in R_0.\mathrm{integers}$ which is regular wherever $\hat\jmath$ is (for every place $P$ of $\overline{F}_{M'}$ over $\overline{\mathbb Q}$, $0 \le \mathrm{ord}_P \hat\jmath$ implies $0 \le \mathrm{ord}_P f$) and whose $R_0$-residue lies in the valuation subring of the place $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O^{\mathrm{SS}}(s)$, and for every $a \in A$ whose residue equals the value $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of that image and $a$ lies in $O^{\mathrm{SS}}(s)$ and in its maximal ideal. `hSS_fix` says each $O^{\mathrm{SS}}(s)$ is invariant under taking preimages along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for every $\zeta' \in \mathrm{Idx}\,q$ and $\gamma \in \Gamma_0(M')$. `hSS_tr` provides, for each $s \in W$, an element $t \in O^{\mathrm{SS}}(s)$ such that $t - a$ lies in $O^{\mathrm{SS}}(s)$ and is a unit there for every $a \in A$.
--
--   A place $s \in W$ is then fixed, together with a field $FSS$ over $\mathrm{ResidueField}\,A$ and a `ComponentChart` $C_b$ for $A$ on $\mathrm{fieldBar}\,q\,M'$ with values in $FSS$ (a valuation subring $C_b.\mathrm{integers}$ with residue map onto $FSS$ whose kernel is the maximal ideal, a set $C_b.\mathrm{dom}$ of places, a finite set $C_b.\mathrm{nodes}$ of places of $FSS$, a place map avoiding the nodes on $C_b.\mathrm{dom}$, the constant-compatibility and scaling axioms, and the pointwise and divisor push-forward compatibilities), subject to `hCb`: $C_b.\mathrm{integers} = O^{\mathrm{SS}}(s)$, and `htr`: $FSS$ contains an element transcendental over $\mathrm{ResidueField}\,A$.
--
--   Two families $An'$ and $An$ of annuli for $A$ on $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb Z/q)$ are given, each consisting of a set of places, a parameter, a modulus in the maximal ideal of $A$ and the axioms of `Annulus` (rationality and the prescribed behaviour of the parameter on the domain, unique realisation of admissible values, $\mathrm{ord}_P(\mathrm{param} - P.\mathrm{evalAt}\,\mathrm{param}) = 1$, and the unit principle), together with an injective family $xt$ of places of $FSS$ over $\mathrm{ResidueField}\,A$. The hypothesis `hAn` says that for each line the two annuli have the same domain and the same modulus, that the modulus is nonzero in $\overline{\mathbb Q}$, and that the product of the two parameters is the constant given by the modulus, so the annuli are reciprocal. The hypothesis `hxt_att` says that for each line the parameter of $An'$ lies in $C_b.\mathrm{integers}$, its $C_b$-residue has order $1$ at $xt$ of that line, and for every $f \in C_b.\mathrm{integers}$ with nonzero $C_b$-residue and $\mathrm{ord}_P f = 0$ at all $P$ in the domain of $An'$ and every such $P$, the product $P.\mathrm{evalAt}\,f \cdot (P.\mathrm{evalAt}\,\mathrm{param})^{-\mathrm{ord}_{xt}(\overline f)}$ lies in $A$ and is a unit of $A$; this is the attachment condition of the regular prolongation underlying $C_b$ at the node $xt$ of that line. The hypothesis `hAn_tube` places the annulus domains in the tube over $s$: for each line, each $P$ in the domain of $An'$, each $f \in R_0.\mathrm{integers}$ regular wherever $\hat\jmath$ is and with $R_0$-residue in the valuation subring of $s$, and each $a \in A$ whose residue is $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference $P.\mathrm{evalAt}$ of the image of $f$ minus $a$ lies in $A$ and in the maximal ideal of $A$.
--
--   Finally, $J$ is an element of $\mathrm{fieldBar}\,q\,M'$ whose Laurent expansion is `jqNModC (AlgebraicClosure ℚ) q`, the $j$-series with its exponents multiplied by $q$, and `hJreg` requires $J$ to be regular wherever $\hat\jmath$ is: for every place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$, $0 \le \mathrm{ord}_P \hat\jmath$ implies $0 \le \mathrm{ord}_P J$. The Hasse datum `hHasse` asserts the existence of a constant $a_0 \in A$ such that $J - a_0$ lies in $C_b.\mathrm{integers}$ with $C_b$-residue zero, of a constant $c' \in \overline{\mathbb Q}$ such that $c'\,(J - a_0)$ lies in $C_b.\mathrm{integers}$ with nonzero $C_b$-residue, and, for every line $\lambda \in \mathbb P^1(\mathbb Z/q)$, of a field $FI$ over $\mathrm{ResidueField}\,A$, a component chart $C$ for $A$ on $\mathrm{fieldBar}\,q\,M'$ with values in $FI$ and a place $x$ of $FI$ over $\mathrm{ResidueField}\,A$ such that $C.\mathrm{integers} = O^{\mathrm{Ig}}(\lambda)$, the annulus $An(\lambda)$ is attached to $C$ at $x$ (that is, $x$ is a node of $C$, the parameter of $An(\lambda)$ is integral with $C$-residue of order $1$ at $x$, and the unit principle of `IsAttached` holds), and $J - a_0$ lies in $C.\mathrm{integers}$ with nonzero $C$-residue and
--   $$\mathrm{ord}_{xt(\lambda)}\bigl(\overline{c'(J-a_0)}^{\,C_b}\bigr) = -\,\mathrm{ord}_x\bigl(\overline{J-a_0}^{\,C}\bigr).$$
--
--   Under these hypotheses the conclusion is: for every line $\lambda \in \mathbb P^1(\mathbb Z/q)$ there exists $g \in \mathrm{fieldBar}\,q\,M'$ such that $g \neq 0$; $g$ is regular wherever $\hat\jmath$ is, i.e. $0 \le \mathrm{ord}_P \hat\jmath$ implies $0 \le \mathrm{ord}_P g$ for every place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$; $g$ lies in $C_b.\mathrm{integers}$ and its $C_b$-residue is zero; both $g$ and $g^{-1}$ lie in $O^{\mathrm{Ig}}(\lambda)$; and $\mathrm{ord}_P g = 0$ for every place $P$ in the domain of $An'(\lambda)$.
--
--   This is the $q = 2$ case, at the rigidifying auxiliary level given by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the construction of a test function on the full-level modular curve over $\overline{\mathbb Q}$ which vanishes identically on the supersingular component chart $C_b$, is a unit of each Igusa valuation ring $O^{\mathrm{Ig}}(\lambda)$ and has no zeros or poles on the corresponding tube annulus; such a function normalises the comparison of the Igusa components with the supersingular component in the Deligne–Rapoport/Igusa description of the reduction of modular curves at $q$. It feeds the assembly of the semistable covering data for the full-level curve, being cited by [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_fullLevelFunction_residue_zero_unit_igusa_ord_zero_tubeAnnulus_jE_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_QAdicPlaceMod

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
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_fullLevelFunction_residue_zero_unit_igusa_ord_zero_tubeAnnulus_jE_of_eq_two_of_dvd
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
    (Cb : ComponentChart A (fieldBar q M') FSS) (hCb : Cb.integers = OSS s) (htr : ∃ t : FSS, Transcendental (ResidueField A) t)
    (An' : CuspidalType.ProjLine q → Annulus A (fieldBar q M')) (xt : CuspidalType.ProjLine q → Place (ResidueField A) FSS)
    (hxt_inj : Function.Injective xt)
    (An : CuspidalType.ProjLine q → Annulus A (fieldBar q M'))
    (hAn : ∀ ℓ, (An' ℓ).dom = (An ℓ).dom ∧ (An' ℓ).modulus = (An ℓ).modulus ∧
      ((An ℓ).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
      (An' ℓ).param * (An ℓ).param = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((An ℓ).modulus : AlgebraicClosure ℚ))
    (hxt_att : ∀ ℓ, ∃ hz : (An' ℓ).param ∈ (⟨Cb.integers, Cb.residue, Cb.algebraMap_mem_iff, Cb.residue_surjective, Cb.ker_residue, Cb.residue_algebraMap,
        Cb.exists_smul_mem⟩ : RegularProlongation A ↥(fieldBar q M') FSS).integers, (xt ℓ).ord ((⟨Cb.integers, Cb.residue, Cb.algebraMap_mem_iff, Cb.residue_surjective, Cb.ker_residue, Cb.residue_algebraMap,
        Cb.exists_smul_mem⟩ : RegularProlongation A ↥(fieldBar q M') FSS).residue ⟨(An' ℓ).param, hz⟩) = 1 ∧
          ∀ (f : fieldBar q M') (hf : f ∈ (⟨Cb.integers, Cb.residue, Cb.algebraMap_mem_iff, Cb.residue_surjective, Cb.ker_residue, Cb.residue_algebraMap,
        Cb.exists_smul_mem⟩ : RegularProlongation A ↥(fieldBar q M') FSS).integers), (⟨Cb.integers, Cb.residue, Cb.algebraMap_mem_iff, Cb.residue_surjective, Cb.ker_residue, Cb.residue_algebraMap,
        Cb.exists_smul_mem⟩ : RegularProlongation A ↥(fieldBar q M') FSS).residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ (An' ℓ).dom, P.ord f = 0) →
              ∀ P ∈ (An' ℓ).dom,
                ∃ h : P.evalAt f * (P.evalAt (An' ℓ).param) ^ (-((xt ℓ).ord ((⟨Cb.integers, Cb.residue, Cb.algebraMap_mem_iff, Cb.residue_surjective, Cb.ker_residue, Cb.residue_algebraMap,
        Cb.exists_smul_mem⟩ : RegularProlongation A ↥(fieldBar q M') FSS).residue ⟨f, hf⟩))) ∈ A,
                  IsUnit (⟨_, h⟩ : A))
    (hAn_tube : ∀ ℓ, ∀ P ∈ (An' ℓ).dom, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (J : ↥(fieldBar q M'))
    (hJ : ((J : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) q)
    (hJreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
      0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) → 0 ≤ P.ord (J : ↥(fieldBar q M')))

    (hHasse : ∃ (a₀ : AlgebraicClosure ℚ) (ha₀ : a₀ ∈ A)
      (hR : ((J : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ Cb.integers),
      Cb.residue ⟨_, hR⟩ = 0 ∧
      ∃ (c' : AlgebraicClosure ℚ) (htc : c' • ((J : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ Cb.integers),
        Cb.residue ⟨_, htc⟩ ≠ 0 ∧
        ∀ ℓ : CuspidalType.ProjLine q, ∃ (FI : Type) (_ : Field FI) (_ : Algebra (ResidueField A) FI)
          (C : ComponentChart A (fieldBar q M') FI) (x : Place (ResidueField A) FI),
          C.integers = OIg ℓ ∧ (An ℓ).IsAttached C x ∧
            ∃ hC : ((J : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ C.integers,
              C.residue ⟨_, hC⟩ ≠ 0 ∧ (xt ℓ).ord (Cb.residue ⟨_, htc⟩) = -(x.ord (C.residue ⟨_, hC⟩)))
    :
    ∀ ℓ : CuspidalType.ProjLine q, ∃ g : ↥(fieldBar q M'),
      g ≠ 0 ∧
      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
        0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) → 0 ≤ P.ord g) ∧
      (∃ h : g ∈ Cb.integers, Cb.residue ⟨g, h⟩ = 0) ∧
      g ∈ OIg ℓ ∧ g⁻¹ ∈ OIg ℓ ∧
      ∀ P ∈ (An' ℓ).dom, P.ord g = 0 := by sorry
