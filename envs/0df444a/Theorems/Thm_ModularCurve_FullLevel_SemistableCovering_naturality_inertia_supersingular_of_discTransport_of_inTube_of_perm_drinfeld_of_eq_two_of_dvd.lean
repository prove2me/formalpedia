-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_naturality_inertia_supersingular_of_discTransport_of_inTube_of_perm_drinfeld_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.SemistableCovering.naturality_inertia_supersingular_of_discTransport_of_inTube_of_perm_drinfeld_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/ede4d845-cf11-5d54-aa6f-dc43afcabaa3
-- title:
--   Inertia naturality on the supersingular charts, q=2
-- statement:
--   Throughout, $q$ is a prime subject to $q = 2$, and $M'$ is a nonzero natural number with $q \nmid M'$; a further prime $\ell$ is given with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Write $\overline{\mathbb Q}$ for `AlgebraicClosure ℚ`. The field $F =$ `fieldBar q M'` is the base change `laurentBaseChange` to $\overline{\mathbb Q}$ of the $\Gamma_H$-function field `xHFunctionField (q^2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, i.e. the units congruent to $1$ modulo $q$; similarly `modularFunctionFieldBar M'` is the base change to $\overline{\mathbb Q}$ of the full modular function field `modularFunctionFieldFull M'`.
--
--   *Base data.* $A$ is a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime q`, that is, $q$ is a nonunit of $A$; $\kappa =$ `ResidueField A`. $W$ is a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$, and `hW` says that $W$ consists exactly of the supersingular places `ssPlaces q M' κ`: those places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathtt{jGeomGen}) \in \mathtt{ssJSet}\,q\,\kappa$. The hypothesis `hle` asserts `modularFunctionFieldBar M' ≤ fieldBar q M'`. $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` (a valuation subring `integers`, a surjective residue map onto the target with kernel the maximal ideal, compatibility with $A$ and with `IsLocalRing.residue A`, a scaling clause, and a place map preserving degrees and orders); `hR₀` says that $R_0$ computes coefficientwise reduction: for every Laurent series $y$ over $A$ whose image in $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ lies in `modularFunctionFieldBar M'`, that element lies in $R_0$.`integers` and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Finally $\zeta$ is an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$.
--
--   *Igusa rings.* $O^{\mathrm{Ig}}$ assigns a valuation subring of $F$ to each point of the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) over $\mathbb Z/q$. Four hypotheses govern it: `hIg_inf` characterises $O^{\mathrm{Ig}}(\infty)$ at the point `lineInfty q` as the set of $f \in F$ admitting Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot y = x$ after pushing $x, y$ forward to $\overline{\mathbb Q}$; `hIg` says that for every line $m$ there is $\gamma \in \Gamma_0(M')$ with $\mathtt{redQ}\,q\,\gamma \cdot \mathtt{lineInfty}\,q = m$ and $O^{\mathrm{Ig}}(m)$ the preimage of $O^{\mathrm{Ig}}(\infty)$ under `levelAutBar q M' ζ γ`; `hIg_inj` says $O^{\mathrm{Ig}}$ is injective; `hIg_perm` says that for every $\zeta'$ in `Idx q` and $\gamma \in \Gamma_0(M')$ the preimages of the $O^{\mathrm{Ig}}(m)$ under `levelAutBar q M' ζ' γ` are again the $O^{\mathrm{Ig}}$, indexed by a permutation of the projective line.
--
--   *Supersingular rings.* $O^{\mathrm{ss}}$ assigns a valuation subring of $F$ to each $s \in W$. Here `hSS_A` says that a constant $x \in \overline{\mathbb Q}$ lies in $O^{\mathrm{ss}}(s)$ if and only if $x \in A$; `hSS_over` says that for $f$ in $R_0$.`integers` which is regular wherever the Laurent expansion $j$ (the image under `coeffEmb` of `jq`) is regular — that is, $0 \le P.\mathrm{ord}(j)$ implies $0 \le P.\mathrm{ord}(f)$ at every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ — and whose $R_0$-residue lies in the valuation subring of the place $s$, the image of $f$ in $F$ lies in $O^{\mathrm{ss}}(s)$, and moreover for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference of the image of $f$ and $a$ lies in the maximal ideal of $O^{\mathrm{ss}}(s)$; `hSS_fix` says each $O^{\mathrm{ss}}(s)$ is its own preimage under every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; `hSS_tr` provides, for each $s$, an element $t \in O^{\mathrm{ss}}(s)$ such that $t - a$ is a unit of $O^{\mathrm{ss}}(s)$ for every $a \in A$.
--
--   *Drinfeld data.* An element $\pi \in \overline{\mathbb Q}$ is given with $\pi^{q^2-1} = q$ and $\pi \in A$, together with a ring homomorphism $\iota : \mathbb F_{q^2} \to \kappa$, and the coordinate ring [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) (the quotient of $\kappa[x_0,x_1]$ by `drinfeldPoly q κ - 1`) is assumed to be a domain.
--
--   *The covering and its charts.* $\mathcal C$ is a `SemistableCovering q M' A W`: a family of component charts `CIg ℓ` over the lines and `CSS s` over $s \in W$, annuli `An ℓ s`, `An' ℓ s`, attachment places `xs`, `xt`, and the compatibility, uniqueness and partition clauses of that structure. The hypothesis `hCIg` identifies the integers of `𝒞.CIg ℓ` with $O^{\mathrm{Ig}}(\ell)$ for every line. For each $s \in W$ a `RegularProlongation` $R^{\mathrm{ss}}_s$ of $A$ from $F$ to `𝒞.FSS s` is given, with `hRSS`: its integers are $O^{\mathrm{ss}}(s)$; `hCSSint`: the integers of `𝒞.CSS s` coincide with those of $R^{\mathrm{ss}}_s$; and `hCSSres`: the two residue maps agree on their common domain.
--
--   *Residue-disc data.* For each $s$ there are a map $\mathrm{disc}_s$ from places of `𝒞.FSS s` over $\kappa$ to sets of places of $F$ over $\overline{\mathbb Q}$, and a coordinate function $\mathrm{coord}_s$ on such places, subject to: `hfamS`, that $R^{\mathrm{ss}}_s$.`DiscFamily` holds for the node set of `𝒞.CSS s`, i.e. for every $Q$ outside the nodes the set $\mathrm{disc}_s(Q)$ is a residue disc over $Q$ with coordinate $\mathrm{coord}_s(Q)$ — the conjunction of `IsDiscCoord`, `PointwiseOn` and `DegreeOn` — and two discs attached to distinct non-node places are disjoint; `htransS`, the transport clause, that for every semilinear automorphism $g$ of $F$ over $\overline{\mathbb Q}$ whose base automorphism preserves $A$ (membership in $A$ is equivalent under it) and induces the identity on $\kappa$ (for $x \in A$ the difference of $g$-image and $x$ lies in the maximal ideal of $A$) and which fixes the element $j$ of $F$, and for every proof that $g$ preserves the integers of $R^{\mathrm{ss}}_s$ and every $\varphi \in \mathrm{Aut}_\kappa(\mathtt{𝒞.FSS }s)$ inducing $g$ on residues and preserving the set of attachment places $\{\mathcal C.\mathtt{xt}\,m\,s\}$, one has for every $Q$ outside that set and every place $P$ of $F$ the equivalence $P \in \mathrm{disc}_s(Q) \iff g \cdot P \in \mathrm{disc}_s(\varphi \cdot Q)$; `hdomS`, that the domain of `𝒞.CSS s` is exactly the union of the $\mathrm{disc}_s(Q)$ over non-node $Q$; `hpmS`, that $P \in \mathrm{disc}_s(Q)$ with $Q$ a non-node forces $\mathtt{placeMap}\,P = Q$; and `hpmS_off`, that `placeMap` takes one and the same value at any two places outside the domain.
--
--   *In-tube clause.* `hAn_tube` requires, for each $s \in W$, each line $m$ and each place $P$ in the domain of the annulus $\mathcal C.\mathtt{An}\,m\,s$: whenever $f$ lies in $R_0$.`integers`, is regular wherever $j$ is (in the sense of `hSS_over`), and has $R_0$-residue in the valuation subring of $s$, then for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that residue, the value $P.\mathrm{evalAt}$ of the image of $f$ in $F$ minus $a$ lies in the maximal ideal of $A$.
--
--   *Node-permutation clause.* `hperm` requires that for every $\tau$ in `A.inertiaSubgroupIn ℚ` (the image in $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup), every $s \in W$ and every $\varphi \in \mathrm{Aut}_\kappa(\mathtt{𝒞.FSS }s)$ such that $\varphi$ induces on the chart `𝒞.CSS s` the arithmetic Galois action of $\tau$ — `InducesOnChart`, i.e. the action preserves the chart's integers and its effect on residues is $\varphi$ — there is a permutation $\sigma$ of the projective line with $\varphi \cdot \mathcal C.\mathtt{xt}\,m\,s = \mathcal C.\mathtt{xt}\,(\sigma m)\,s$ for all $m$.
--
--   *Conclusion.* The assertion is the conjunction of two statements, where for $\tau$ in the inertia subgroup $g_\tau$ denotes [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54), the semilinear automorphism of $F$ acting coefficientwise by $\tau$ on Laurent series.
--
--   First: for every $\tau \in$ `A.inertiaSubgroupIn ℚ` and every $s \in W$, (i) an element $f \in F$ lies in the integers of `𝒞.CSS s` if and only if $g_\tau \cdot f$ does; (ii) a place $P$ lies in the domain of `𝒞.CSS s` if and only if $g_\tau \cdot P$ does; and (iii) there exists $\varphi \in \mathrm{Aut}_\kappa(\mathtt{𝒞.FSS }s)$ such that $\varphi$ induces $g_\tau$ on the chart `𝒞.CSS s` in the sense of `InducesOnChart`, and such that for every $P$ in the domain of the chart, $\mathtt{placeMap}(g_\tau \cdot P) = (\mathtt{SemilinearAut.ofAlgAut }\varphi) \cdot \mathtt{placeMap}(P)$.
--
--   Second: for every $\tau \in$ `A.inertiaSubgroupIn ℚ` with $A.\mathtt{tameCharacter}\,\pi\,\tau = 1$ (the residue of $\tau(\pi)/\pi$ in $\kappa$, taken to be $0$ when $\tau(\pi)/\pi \notin A$) and every $s \in W$: the action $g_\tau$ induces on the chart `𝒞.CSS s` the identity automorphism of `𝒞.FSS s`, and for every non-node place $Q$ of `𝒞.FSS s` and every place $P$ of $F$ one has $P \in \mathrm{disc}_s(Q)$ if and only if $g_\tau \cdot P \in \mathrm{disc}_s(Q)$, so that each residue disc is stable under $g_\tau$.
--
--   This is the naturality statement for the action of inertia at $q$ on the supersingular (Drinfeld) charts of a semistable covering of the function field of $X_H(q^2M')$ in the case $q = 2$, at an auxiliary level rigidified by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$: the inertia action preserves each chart, permutes its nodes through an automorphism of the reduced field, and acts trivially on the charts and on their residue discs once the tame character at $\pi$ is trivial. It is used in the assembly of the semistable covering together with its equivariance clauses, in [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_naturality_inertia_supersingular_of_discTransport_of_inTube_of_perm_drinfeld_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.SemistableCovering.naturality_inertia_supersingular_of_discTransport_of_inTube_of_perm_drinfeld_of_eq_two_of_dvd
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
