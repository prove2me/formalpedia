-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_naturality_inertia_supersingular_of_discTransport_of_inTube_of_perm_drinfeld_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.SemistableCovering.naturality_inertia_supersingular_of_discTransport_of_inTube_of_perm_drinfeld_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/de2915de-6ea2-56f7-ba63-84c974ff84f0
-- title:
--   Inertia naturality on the supersingular charts, q=3
-- statement:
--   Throughout, $q$ is a prime with $q = 3$, $M'$ is a nonzero natural number with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ is fixed. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a nonunit of $A$; $\kappa =$ `ResidueField A` is its residue field. $W$ is a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$, and `hW` says that $W$ consists exactly of the supersingular places `ssPlaces q M' κ`, i.e. of the rational affine geometric places at which the value of `jGeomGen` lies in `ssJSet q κ`. The two function fields in play are $\bar F_0 =$ `modularFunctionFieldBar M'`, the Laurent base change to $\overline{\mathbb{Q}}$ of the full-level field `modularFunctionFieldFull M'`, and $\bar F =$ `fieldBar q M'`, the Laurent base change to $\overline{\mathbb{Q}}$ of `xHFunctionField (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction map $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/q)^{\times}$, that is, the group of units congruent to $1$ modulo $q$; the hypothesis `hle` is the inclusion $\bar F_0 \le \bar F$ of intermediate fields.
--
--   The reduction datum consists of a `ConstantReduction` $R_0$ of $A$ from $\bar F_0$ to `modularFunctionFieldC κ M'` (a valuation subring $R_0.\mathrm{integers}$ of $\bar F_0$, a surjective residue map onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, a place map, and the compatibility axioms of that structure), together with the hypothesis `hR₀`: for every Laurent series $y$ over $A$ whose coefficientwise image in `LaurentSeries (AlgebraicClosure ℚ)` lies in $\bar F_0$, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$. Finally $\zeta$ is an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$.
--
--   Two families of valuation subrings of $\bar F$ are given: $O^{\mathrm{Ig}}$ indexed by $\mathbb{P}^1(\mathbb{F}_q) =$ [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21), and $O^{\mathrm{ss}}$ indexed by $W$. (In the hypotheses `hIg` and `hIg_perm` the bound variable written `ℓ` ranges over [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21), shadowing the fixed prime.) The Igusa clauses are: `hIg_inf`, which describes $O^{\mathrm{Ig}}(\infty)$ at the line `lineInfty q` $= [1:0]$ as the set of $f \in \bar F$ for which there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot y = x$ in `LaurentSeries (AlgebraicClosure ℚ)`; `hIg`, which provides for each line $\mathfrak{l}$ some $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` carries $[1:0]$ to $\mathfrak{l}$ and with $O^{\mathrm{Ig}}(\mathfrak{l})$ the pullback of $O^{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`; `hIg_inj`, the injectivity of $O^{\mathrm{Ig}}$; and `hIg_perm`, which for each $\zeta'$ in `Idx q` and each $\gamma \in \Gamma_0(M')$ produces a permutation $\sigma$ of $\mathbb{P}^1(\mathbb{F}_q)$ with the pullback of $O^{\mathrm{Ig}}(\mathfrak{l})$ along `levelAutBar q M' ζ' γ` equal to $O^{\mathrm{Ig}}(\sigma \mathfrak{l})$.
--
--   The supersingular clauses are: `hSS_A`, saying that for each $s$ the contraction of $O^{\mathrm{ss}}_s$ along the structure map $\overline{\mathbb{Q}} \to \bar F$ is $A$; `hSS_over`, saying that for $s \in W$ and $f \in R_0.\mathrm{integers}$ which is regular wherever the image of the $q$-expansion of $j$ is (every place $P$ of $\bar F_0$ over $\overline{\mathbb{Q}}$ with $P.\mathrm{ord}$ of that element nonnegative has $P.\mathrm{ord}(f) \ge 0$) and whose $R_0$-residue lies in the valuation subring of the place $s$, the image of $f$ in $\bar F$ lies in $O^{\mathrm{ss}}_s$, and for every $a \in A$ whose residue equals the value $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of that image and $a$ lies in $O^{\mathrm{ss}}_s$ and in its maximal ideal; `hSS_fix`, the invariance of $O^{\mathrm{ss}}_s$ under pullback along `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$; and `hSS_tr`, which provides for each $s$ an element $t \in O^{\mathrm{ss}}_s$ such that $t - a$ lies in $O^{\mathrm{ss}}_s$ and is a unit there for every $a \in A$.
--
--   The Drinfeld data are an element $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2-1} = q$ and $\pi \in A$, a ring homomorphism $\iota : \mathbb{F}_{q^2} =$ `GaloisField q 2` $\to \kappa$, and the assumption that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain.
--
--   Next, $\mathcal{C}$ is a `SemistableCovering q M' A W`: Igusa charts `𝒞.CIg ℓ` with reduced fields `𝒞.FIg ℓ`, supersingular charts `𝒞.CSS s` with reduced fields `𝒞.FSS s`, annuli `𝒞.An`, `𝒞.An'`, attachment places `𝒞.xs`, `𝒞.xt`, and the axioms of that structure. The chart identifications are `hCIg`, that the ring of `𝒞.CIg ℓ` is $O^{\mathrm{Ig}}(\mathfrak{l})$; a family $R^{\mathrm{ss}}_s$ of regular prolongations of $A$ from $\bar F$ to `𝒞.FSS s`; `hRSS`, that the ring of $R^{\mathrm{ss}}_s$ is $O^{\mathrm{ss}}_s$; `hCSSint`, that the ring of `𝒞.CSS s` equals that of $R^{\mathrm{ss}}_s$; and `hCSSres`, that the two residue maps agree on common arguments.
--
--   The residue-disc data are maps $\mathrm{disc}_s$ from places of `𝒞.FSS s` over $\kappa$ to sets of places of $\bar F$ over $\overline{\mathbb{Q}}$ and coordinate functions $\mathrm{coord}_s$ into $\bar F$, subject to: `hfamS`, that $(\mathrm{disc}_s, \mathrm{coord}_s)$ is a `DiscFamily` for $R^{\mathrm{ss}}_s$ relative to the nodes of `𝒞.CSS s`, i.e. for every non-node $Q$ the set $\mathrm{disc}_s(Q)$ is a residue disc with coordinate $\mathrm{coord}_s(Q)$ and the discs attached to distinct non-nodes are disjoint; `htransS`, the transport clause, which states for each $s$ that for every semilinear automorphism $g$ of $\bar F$ over $\overline{\mathbb{Q}}$ whose base automorphism preserves $A$ and is trivial on the residue field of $A$ (for $x \in A$ the difference $g(x) - x$ lies in the maximal ideal), which fixes the image in $\bar F$ of the $q$-expansion of $j$, which preserves the ring of $R^{\mathrm{ss}}_s$, and for every $\kappa$-algebra automorphism $\varphi$ of `𝒞.FSS s` computing the $R^{\mathrm{ss}}_s$-residue of $g \cdot f$ from that of $f$ and preserving the set of attachment places $\{\mathcal{C}.\mathrm{xt}\,\mathfrak{l}\,s\}$, one has for every $Q$ outside that set and every place $P$ of $\bar F$ the equivalence $P \in \mathrm{disc}_s(Q) \iff g \cdot P \in \mathrm{disc}_s(\varphi \cdot Q)$; `hdomS`, that $P$ lies in the domain of `𝒞.CSS s` precisely when $P \in \mathrm{disc}_s(Q)$ for some non-node $Q$; `hpmS`, that the place map of `𝒞.CSS s` sends $P \in \mathrm{disc}_s(Q)$ to $Q$ for non-node $Q$; and `hpmS_off`, that the place map of `𝒞.CSS s` is constant on the complement of its domain.
--
--   The remaining two hypotheses are `hAn_tube`, the in-tube clause: for every $s \in W$, every $\mathfrak{l} \in \mathbb{P}^1(\mathbb{F}_q)$ and every place $P$ in the domain of the annulus $\mathcal{C}.\mathrm{An}\,\mathfrak{l}\,s$, and for every $f \in R_0.\mathrm{integers}$ satisfying the same $j$-regularity and residue conditions as in `hSS_over`, and every $a \in A$ whose residue is the value of the $R_0$-residue of $f$ at $s$, the element $P.\mathrm{evalAt}$ of the image of $f$ in $\bar F$ minus $a$ lies in $A$ and in its maximal ideal; and `hperm`, the node-permutation clause: for every $\tau$ in `A.inertiaSubgroupIn ℚ`, every $s$ and every $\kappa$-algebra automorphism $\varphi$ of `𝒞.FSS s`, if $\varphi$ `InducesOnChart` the chart `𝒞.CSS s` for the arithmetic Galois action of $\tau$ on $\bar F$ — that is, that action preserves the chart's ring and $\varphi$ computes the chart residue of the translated element — then there is a permutation of $\mathbb{P}^1(\mathbb{F}_q)$ under which $\varphi$ permutes the attachment places $\mathcal{C}.\mathrm{xt}\,\mathfrak{l}\,s$.
--
--   Under all of this, the conclusion is the conjunction of two statements about the semilinear automorphisms $g_\tau =$ `arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ` of $\bar F$, given by letting $\tau$ act coefficientwise on Laurent series.
--
--   First: for every $\tau \in$ `A.inertiaSubgroupIn ℚ` and every $s \in W$, writing $g = g_\tau$: (i) for all $f \in \bar F$, $f$ lies in the ring of `𝒞.CSS s` if and only if $g \cdot f$ does; (ii) for all places $P$ of $\bar F$ over $\overline{\mathbb{Q}}$, $P$ lies in the domain of `𝒞.CSS s` if and only if $g \cdot P$ does; and (iii) there exists a $\kappa$-algebra automorphism $\varphi$ of `𝒞.FSS s` which `InducesOnChart` the chart `𝒞.CSS s` for $g$ and satisfies, for every $P$ in the domain of `𝒞.CSS s`, the identity $\mathrm{placeMap}(g \cdot P) = \mathrm{ofAlgAut}(\varphi) \cdot \mathrm{placeMap}(P)$ for the place map of `𝒞.CSS s`.
--
--   Second: for every $\tau \in$ `A.inertiaSubgroupIn ℚ` with tame character $A.\mathrm{tameCharacter}\,\pi\,\tau = 1$ (the residue of $\tau(\pi)/\pi$ in $\kappa$, taken to be $0$ when that quotient is not in $A$) and every $s \in W$: the identity ring automorphism of `𝒞.FSS s` `InducesOnChart` the chart `𝒞.CSS s` for $g_\tau$, and for every non-node $Q$ and every place $P$ of $\bar F$ one has $P \in \mathrm{disc}_s(Q) \iff g_\tau \cdot P \in \mathrm{disc}_s(Q)$.
--
--   This is the $q = 3$ form, at the rigid auxiliary level provided by the prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the inertia-equivariance statement for the supersingular (Drinfeld) charts in the semistable covering of $X_H(q^2M')$ over a valuation ring above $q$: inertia preserves each supersingular chart, acts on its reduction through an algebra automorphism compatible with the place map, and acts trivially on the chart and on each residue disc once its tame character is trivial. It feeds the construction of a semistable covering together with its full list of equivariance clauses, [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_naturality_inertia_supersingular_of_discTransport_of_inTube_of_perm_drinfeld_of_eq_three_of_dvd.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.SemistableCovering.naturality_inertia_supersingular_of_discTransport_of_inTube_of_perm_drinfeld_of_eq_three_of_dvd
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField A)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField A))]
    (𝒞 : SemistableCovering q M' A W)
    (hCIg : ∀ ℓ, (𝒞.CIg ℓ).integers = OIg ℓ)
    (RSS : ∀ s : ↥W, RegularProlongation A (fieldBar q M') (𝒞.FSS s))
    (hRSS : ∀ s, (RSS s).integers = OSS s)
    (hCSSint : ∀ s, (𝒞.CSS s).integers = (RSS s).integers)
    (hCSSres : ∀ s (f : fieldBar q M') (hC : f ∈ (𝒞.CSS s).integers) (hR : f ∈ (RSS s).integers),
      (𝒞.CSS s).residue ⟨f, hC⟩ = (RSS s).residue ⟨f, hR⟩)
    (discS : ∀ s : ↥W, Place (ResidueField A) (𝒞.FSS s) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (coordS : ∀ s : ↥W, Place (ResidueField A) (𝒞.FSS s) → (fieldBar q M'))
    (hfamS : ∀ s, (RSS s).DiscFamily (𝒞.CSS s).nodes (discS s) (coordS s))
    (htransS : ∀ s, (∀ g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'),
        (∀ x : AlgebraicClosure ℚ, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A) →
        (∀ x : ↥A, ∃ h : SemilinearAut.baseAut g (x : AlgebraicClosure ℚ) ∈ A, (⟨_, h⟩ : ↥A) - x ∈ maximalIdeal ↥A) →
        g • (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) = (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) →
        ∀ (hst : ∀ f : ↥(fieldBar q M'), f ∈ (RSS s).integers ↔ g • f ∈ (RSS s).integers)
          (φ : (𝒞.FSS s) ≃ₐ[ResidueField A] (𝒞.FSS s)),
        (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (RSS s).integers), (RSS s).residue ⟨g • f, (hst f).mp hf⟩ = φ ((RSS s).residue ⟨f, hf⟩)) →
        (∀ Q : Place (ResidueField A) (𝒞.FSS s), φ • Q ∈ Set.range (fun ℓ => 𝒞.xt ℓ s) ↔ Q ∈ Set.range (fun ℓ => 𝒞.xt ℓ s)) →
        ∀ (Q : Place (ResidueField A) (𝒞.FSS s)), Q ∉ Set.range (fun ℓ => 𝒞.xt ℓ s) →
          ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ discS s Q ↔ g • P ∈ discS s (φ • Q)))
    (hdomS : ∀ s P, P ∈ (𝒞.CSS s).dom ↔ ∃ Q, Q ∉ (𝒞.CSS s).nodes ∧ P ∈ discS s Q)
    (hpmS : ∀ s P Q, Q ∉ (𝒞.CSS s).nodes → P ∈ discS s Q → (𝒞.CSS s).placeMap P = Q)
    (hpmS_off : ∀ s P P', P ∉ (𝒞.CSS s).dom → P' ∉ (𝒞.CSS s).dom → (𝒞.CSS s).placeMap P = (𝒞.CSS s).placeMap P')

    (hAn_tube : ∀ (s : ↥W) (ℓ : CuspidalType.ProjLine q), ∀ P ∈ (𝒞.An ℓ s).dom, (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A))

    (hperm : ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ (s : ↥W) (φ : 𝒞.FSS s ≃ₐ[ResidueField A] 𝒞.FSS s),
      SemistableCovering.InducesOnChart (𝒞.CSS s)
        (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) φ.toRingEquiv →
      ∃ π : Equiv.Perm (CuspidalType.ProjLine q), ∀ ℓ, φ • 𝒞.xt ℓ s = 𝒞.xt (π ℓ) s) :
    (∀ τ ∈ A.inertiaSubgroupIn ℚ,
      let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
      ∀ s, (∀ f : fieldBar q M', f ∈ (𝒞.CSS s).integers ↔ g • f ∈ (𝒞.CSS s).integers) ∧
        (∀ P, P ∈ (𝒞.CSS s).dom ↔ g • P ∈ (𝒞.CSS s).dom) ∧
        ∃ φ : 𝒞.FSS s ≃ₐ[ResidueField A] 𝒞.FSS s, SemistableCovering.InducesOnChart (𝒞.CSS s) g φ.toRingEquiv ∧
          ∀ P ∈ (𝒞.CSS s).dom, (𝒞.CSS s).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (𝒞.CSS s).placeMap P) ∧
    (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ s, SemistableCovering.InducesOnChart (𝒞.CSS s) (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _) ∧
        ∀ Q, Q ∉ (𝒞.CSS s).nodes → ∀ P, P ∈ discS s Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ discS s Q) := by sorry
