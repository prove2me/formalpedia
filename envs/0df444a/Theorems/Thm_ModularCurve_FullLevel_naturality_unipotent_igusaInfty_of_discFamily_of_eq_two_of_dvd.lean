-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_naturality_unipotent_igusaInfty_of_discFamily_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.naturality_unipotent_igusaInfty_of_discFamily_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/341e924c-8b69-5069-87ef-589c3bbe2ca8
-- title:
--   Unipotent level automorphisms at the Igusa chart of ∞, q=2
-- statement:
--   Throughout, $q$ is a prime with $q = 2$; $M'$ is a non-zero natural number not divisible by $q$; $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$; and $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. the image of $q$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$. Write $k =$ `ResidueField A`. The two function fields in play are, on the characteristic-zero side, $F =$ `fieldBar q M'`, the intermediate field of `LaurentSeries (AlgebraicClosure ℚ)` over $\overline{\mathbb{Q}}$ obtained as the base change `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')` of the $X_H$-function field of level $q^2M'$ with $H =$ `levelH q M'` the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ (the units congruent to $1$ modulo $q$), and, on the reduction side, $\bar F =$ `xHFunctionFieldC k (q ^ 2 * M') (levelH q M')`, together with the level-$M'$ modular function fields `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ and `modularFunctionFieldC k M'` over $k$.
--
--   *Supersingular places and the constant reduction.* A finite set $W$ of places of `modularFunctionFieldC k M'` over $k$ is given, with `hW` asserting that $W$ is exactly `ssPlaces q M' k`, the set of places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathtt{jGeomGen}) \in \mathtt{ssJSet}\,q$. The hypothesis `hle` is the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`. Further, $R_0$ is a `ConstantReduction` of `modularFunctionFieldBar M'` to `modularFunctionFieldC k M'` relative to $A$: a valuation subring `R₀.integers`, a surjective residue homomorphism onto `modularFunctionFieldC k M'` whose kernel is the maximal ideal, compatibility of integrality and of residues with $A \to k$ on constants, the normalisation clause producing for each non-zero $f$ a scalar $c$ with $c \cdot f$ integral of non-zero residue, and a place map preserving degrees and pushing forward principal divisors. The hypothesis `hR₀` says that this residue map is computed coefficientwise on Laurent series: for every $y \in$ `LaurentSeries A` whose coefficientwise image lies in `modularFunctionFieldBar M'`, that image is in `R₀.integers` and its $R_0$-residue, viewed in `LaurentSeries k`, is the coefficientwise reduction of $y$.
--
--   *Igusa rings.* An index $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) is fixed, together with families $O_{\mathrm{Ig}}$ of valuation subrings of $F$ indexed by the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) over $\mathbb{Z}/q$ and $O_{\mathrm{SS}}$ of valuation subrings of $F$ indexed by $W$. The Igusa group of hypotheses is: `hIg_inf`, which describes $O_{\mathrm{Ig}}(\mathtt{lineInfty}\,q)$ as the set of $f \in F$ expressible as a ratio $x/y$ of Laurent series with coefficients in $A$ whose denominator has non-zero coefficientwise reduction, in the sense that $f \cdot y = x$ after pushing coefficients into $\overline{\mathbb{Q}}$; `hIg`, which for each point of the projective line (the bound variable there, also named $\ell$, ranges over [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21)) provides $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` moves `lineInfty q` to that point and for which the corresponding Igusa ring is the pullback of $O_{\mathrm{Ig}}(\mathtt{lineInfty}\,q)$ along `levelAutBar q M' ζ γ`; `hIg_inj`, the injectivity of $O_{\mathrm{Ig}}$; and `hIg_perm`, which asserts that for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ pullback along `levelAutBar q M' ζ' γ` permutes the family $O_{\mathrm{Ig}}$ through some permutation of the projective line.
--
--   *Supersingular rings.* The group of hypotheses on $O_{\mathrm{SS}}$ consists of: `hSS_A`, that for each $s \in W$ an element of $\overline{\mathbb{Q}}$ lies in $O_{\mathrm{SS}}(s)$ (after the structure map) if and only if it lies in $A$; `hSS_over`, which for $s \in W$ and $f \in R_0.\mathtt{integers}$ that is integral at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ at which the coefficientwise image of `jq` is integral, and whose $R_0$-residue lies in the valuation subring of the place $s$, asserts both that the image of $f$ in $F$ lies in $O_{\mathrm{SS}}(s)$ and that for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue the difference of the image of $f$ and the constant $a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$; `hSS_fix`, that each $O_{\mathrm{SS}}(s)$ is its own pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; and `hSS_tr`, which provides for each $s$ an element $t \in O_{\mathrm{SS}}(s)$ such that $t$ minus any constant from $A$ is a unit of $O_{\mathrm{SS}}(s)$.
--
--   *Charts at the Igusa components.* Component charts $C_{\mathrm{Ig}}$ indexed by the projective line and a single chart $C_\infty$, all of type `ComponentChart A (fieldBar q M') (xHFunctionFieldC k (q ^ 2 * M') (levelH q M'))`, are given, together with a `RegularProlongation` $R_I$ of the same data. The hypotheses are: `hRI`, that $R_I.\mathtt{integers} = O_{\mathrm{Ig}}(\mathtt{lineInfty}\,q)$; `hCinfint` and `hCinfres`, that $C_\infty$ has the same ring of integers as $R_I$ and the same residue map on it. Next, a finite set $N_{\mathrm{Ig}}$ of places of $\bar F$ over $k$, an assignment $\mathrm{disc}_I$ of sets of places of $F$ over $\overline{\mathbb{Q}}$ to places of $\bar F$, and a coordinate function $\mathrm{coord}_I$ with values in $F$ are given, subject to `hnodesI`, that $C_\infty.\mathtt{nodes} = N_{\mathrm{Ig}}$, and `hfamI`, that $(N_{\mathrm{Ig}}, \mathrm{disc}_I, \mathrm{coord}_I)$ is a `DiscFamily` for $R_I$: each $Q \notin N_{\mathrm{Ig}}$ has $\mathrm{disc}_I(Q)$ a residue disc with coordinate $\mathrm{coord}_I(Q)$, and discs attached to distinct $Q, Q' \notin N_{\mathrm{Ig}}$ are disjoint. Subrings $S_I(Q) \subseteq F$ and ring homomorphisms $\chi_{0,I}(Q) : S_I(Q) \to k$ are given, with `hstalkI` asserting for $Q \notin N_{\mathrm{Ig}}$ that every element of $S_I(Q)$ lies in $R_I.\mathtt{integers}$ and that a place $P$ belongs to $\mathrm{disc}_I(Q)$ precisely when $P$ is rational, every element of $S_I(Q)$ is $P$-integral with $P$-value in $A$, and for every $f \in S_I(Q)$ the $A$-valuation of $P.\mathrm{evalAt}(f)$ is $< 1$ if and only if $\chi_{0,I}(Q)(f) = 0$. The chart is tied to this family by `hdomI`, that $P \in C_\infty.\mathtt{dom}$ iff $P \in \mathrm{disc}_I(Q)$ for some $Q \notin N_{\mathrm{Ig}}$; `hpmI`, that $C_\infty.\mathtt{placeMap}$ sends $\mathrm{disc}_I(Q)$ to $Q$ for $Q \notin N_{\mathrm{Ig}}$; and `hpmI_off`, that $C_\infty.\mathtt{placeMap}$ is constant outside $C_\infty.\mathtt{dom}$. Equivariance is expressed by `hNstabI` and `hdiscstabI`: for every $\tau$ in the subgroup of $\overline{\mathbb{Q}}$-automorphisms of $F$ generated by the elements `levelAutBar q M' ζ' γ` with $\zeta' \in$ `Idx q` and $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves $R_I.\mathtt{integers}$, the induced automorphism $R_I.\mathtt{resAut}\,\tau$ of $\bar F$ preserves $N_{\mathrm{Ig}}$, and for $Q \notin N_{\mathrm{Ig}}$ the translate `RegularProlongation.smulDisc τ (discI Q)` equals $\mathrm{disc}_I$ of the translated place. Finally, automorphisms $g(\cdot)$ of $F$ over $\overline{\mathbb{Q}}$ indexed by the projective line are given, with `hg` placing each $g(\cdot)$ in that subgroup and exhibiting it as `levelAutBar q M' ζ γ` for some $\gamma \in \Gamma_0(M')$ carrying `lineInfty q` to the given point under `redQ q`, and `hCIg_def` identifying $C_{\mathrm{Ig}}$ at each point with the comap chart $C_\infty.\mathtt{comap}$ along $g$ at that point (integers pulled back, domain $\{P : g \bullet P \in C_\infty.\mathtt{dom}\}$, place map $P \mapsto C_\infty.\mathtt{placeMap}(g \bullet P)$, nodes unchanged).
--
--   *The unipotent chart hypothesis.* The last hypothesis `huni` states: for every $\zeta' \in$ `Idx q` and every $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` equals [`CuspidalType.unipotent q t`](def/CuspidalType_IsCuspidalOfType.html#L27) for some $t \in \mathbb{Z}/q$, the semilinear automorphism `SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹)` — the pair consisting of that automorphism of $F$ and the identity of $\overline{\mathbb{Q}}$ — satisfies `SemistableCovering.InducesOnChart` for the chart $C_{\mathrm{Ig}}(\mathtt{lineInfty}\,q)$ with the identity of $\bar F$, i.e. it preserves the ring of integers of that chart and induces the identity on its residue field.
--
--   *Conclusion.* For every $\zeta' \in$ `Idx q` and every $\gamma \in \Gamma_0(M')$ such that `redQ q γ = CuspidalType.unipotent q t` for some $t \in \mathbb{Z}/q$, writing $\sigma =$ `SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹)` and $C = C_{\mathrm{Ig}}(\mathtt{lineInfty}\,q)$, the following three statements hold: first, for every place $P$ of $F$ over $\overline{\mathbb{Q}}$ one has $P \in C.\mathtt{dom}$ if and only if $\sigma \bullet P \in C.\mathtt{dom}$; second, `SemistableCovering.InducesOnChart C σ (RingEquiv.refl _)` holds, that is, $\sigma$ preserves $C.\mathtt{integers}$ and acts as the identity on the residues of its elements; third, for every $P \in C.\mathtt{dom}$ one has $C.\mathtt{placeMap}(\sigma \bullet P) = C.\mathtt{placeMap}(P)$. The second conjunct is the hypothesis `huni` at the same $\zeta'$, $\gamma$; the content of the statement is the addition of the first and third conjuncts.
--
--   This is the naturality clause, for unipotent reductions and at the Igusa component indexed by `lineInfty q`, in the assembly of a semistable covering of the modular curve of level $q^2M'$ with $H$ the units congruent to $1$ modulo $q$, in the case $q = 2$ where $M'$ carries a prime $\ell \equiv 11 \pmod{12}$; it records that an automorphism which is trivial on the reduction of the $\infty$-chart also fixes that chart's domain and place map. It is used by [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd), the existence statement for the semistable covering together with its equivariance clauses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_naturality_unipotent_igusaInfty_of_discFamily_of_eq_two_of_dvd.lean

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
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.naturality_unipotent_igusaInfty_of_discFamily_of_eq_two_of_dvd
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
    (CIg : CuspidalType.ProjLine q → ComponentChart A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (Cinf : ComponentChart A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (RI : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hRI : RI.integers = OIg (lineInfty q))
    (hCinfint : Cinf.integers = RI.integers)
    (hCinfres : ∀ (f : fieldBar q M') (hC : f ∈ Cinf.integers) (hR : f ∈ RI.integers), Cinf.residue ⟨f, hC⟩ = RI.residue ⟨f, hR⟩)
    (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
    (discI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (coordI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → (fieldBar q M'))
    (hnodesI : Cinf.nodes = NIg) (hfamI : RI.DiscFamily NIg discI coordI)
    (SI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Subring (fieldBar q M'))
    (χ₀I : ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), ↥(SI Q) →+* ResidueField A)
    (hstalkI : (∀ Q, Q ∉ NIg → (∀ f : ↥(SI Q), (f : fieldBar q M') ∈ RI.integers) ∧
        ∀ P, P ∈ discI Q ↔ P.IsRational ∧
          (∀ f : ↥(SI Q), (f : fieldBar q M') ∈ P.toValuationSubring ∧ P.evalAt (f : fieldBar q M') ∈ A) ∧
          (∀ f : ↥(SI Q), A.valuation (P.evalAt (f : fieldBar q M')) < 1 ↔ χ₀I Q f = 0)))
    (hdomI : ∀ P, P ∈ Cinf.dom ↔ ∃ Q, Q ∉ NIg ∧ P ∈ discI Q)
    (hpmI : ∀ P Q, Q ∉ NIg → P ∈ discI Q → Cinf.placeMap P = Q)
    (hpmI_off : ∀ P P', P ∉ Cinf.dom → P' ∉ Cinf.dom → Cinf.placeMap P = Cinf.placeMap P')
    (hNstabI : ∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ RI.integers ↔ f ∈ RI.integers)
      (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), RI.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg)
    (hdiscstabI : ∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ RI.integers ↔ f ∈ RI.integers)
      (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), Q ∉ NIg → RegularProlongation.smulDisc τ (discI Q) = discI (RI.resAut τ hτ • Q))
    (g : CuspidalType.ProjLine q → ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')))
    (hg : ∀ ℓ, g ℓ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}) ∧ ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧ g ℓ = levelAutBar q M' ζ γ)
    (hCIg_def : ∀ ℓ, CIg ℓ = Cinf.comap (g ℓ))

    (huni : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t) →
      SemistableCovering.InducesOnChart (CIg (lineInfty q)) (SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹)) (RingEquiv.refl _)) :
    ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t) →
      (∀ P, P ∈ (CIg (lineInfty q)).dom ↔ SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹) • P ∈ (CIg (lineInfty q)).dom) ∧
      SemistableCovering.InducesOnChart (CIg (lineInfty q)) (SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹)) (RingEquiv.refl _) ∧
      (∀ P ∈ (CIg (lineInfty q)).dom,
        (CIg (lineInfty q)).placeMap (SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹) • P) = (CIg (lineInfty q)).placeMap P) := by sorry
