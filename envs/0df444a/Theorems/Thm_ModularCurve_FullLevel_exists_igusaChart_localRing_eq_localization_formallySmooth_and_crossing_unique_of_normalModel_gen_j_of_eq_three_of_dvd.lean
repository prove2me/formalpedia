-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/5ce6e52e-6b69-5e11-8f2e-f17e1ce206d9
-- title:
--   Igusa charts and crossing uniqueness on the descended curve, q=3
-- statement:
--   Throughout, $q$ is a prime with $q = 3$, and $M'$ is a nonzero natural number with $q \nmid M'$; in addition an auxiliary prime $\ell$ is fixed with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ (the rigidity guard for small $q$; the final binder of the statement re-uses the name `ℓ` for a point of the projective line, shadowing this prime). The field `fieldBar q M'` is the base change to $\bar{\mathbb{Q}}$ of the function field of the modular curve $X_H$ of level $q^2M'$, where $H \le (\mathbb{Z}/q^2M')^\times$ is the kernel of reduction to $(\mathbb{Z}/q)^\times$, realised inside $\bar{\mathbb{Q}}((t))$; `modularFunctionFieldBar M'` is the base change to $\bar{\mathbb{Q}}$ of the full level-$M'$ modular function field, and `modularFunctionFieldC k M'` is the subfield of $k((t))$ generated over $k$ by the $q$-expansions of $j$ and of $j$ at level $M'$.
--
--   The arithmetic input is: a valuation subring $A$ of $\bar{\mathbb{Q}}$ with $q$ a non-unit of $A$ (`hA`); a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$ which, by `hW`, consists exactly of the supersingular places, i.e. of those places $w$ that are rational, are affine geometric places, and whose value at the geometric $j$-generator lies in the supersingular $j$-set for $q$; the inclusion `hle` of `modularFunctionFieldBar M'` in `fieldBar q M'`; a constant reduction datum $R_0$ for $A$ on `modularFunctionFieldBar M'` with residue target `modularFunctionFieldC (ResidueField A) M'`, that is, a valuation subring `R₀.integers` whose intersection with the constants is $A$, a surjective residue homomorphism onto the level-$M'$ function field over the residue field of $A$ with kernel the maximal ideal, compatible with the residue map of $A$ on constants, together with a map `placeMap` on places preserving degrees and compatible with order divisors, and a clause producing for every nonzero element a constant multiple with nonzero residue; the hypothesis `hR₀`, which asserts that for a Laurent series $y$ over $A$ whose coefficientwise image in $\bar{\mathbb{Q}}((t))$ lies in `modularFunctionFieldBar M'`, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$; an element $\pi \in A$ with $\pi^{q^2-1} = q$; and a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`).
--
--   Two families of valuation subrings of `fieldBar q M'` are given: $O^{\mathrm{Ig}}$ indexed by the projective line $\mathbb{P}^1(\mathbb{Z}/q)$ and $O^{\mathrm{SS}}$ indexed by $W$. The hypotheses on $O^{\mathrm{Ig}}$ are: `hIg_inf`, that $f \in O^{\mathrm{Ig}}(\infty)$ holds precisely when $f$ can be written as a ratio of Laurent series with coefficients in $A$, namely when there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot y = x$ in $\bar{\mathbb{Q}}((t))$; `hIg`, that each index is reached from $\infty$ by some $\gamma \in \Gamma_0(M')$, whose reduction mod $q$ moves `lineInfty q` to that index and for which $O^{\mathrm{Ig}}$ at the index is the preimage of $O^{\mathrm{Ig}}(\infty)$ under `levelAutBar q M' ζ γ`; `hIg_inj`, injectivity of $O^{\mathrm{Ig}}$; and `hIg_perm`, that for every root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the operation of taking preimages under `levelAutBar q M' ζ' γ` permutes the family $O^{\mathrm{Ig}}$. The hypotheses on $O^{\mathrm{SS}}$ are: `hSS_A`, that a constant of $\bar{\mathbb{Q}}$ lies in $O^{\mathrm{SS}}(s)$ iff it lies in $A$; `hSS_over`, that for $s \in W$ and $f$ in `R₀.integers` having non-negative order at every place of `modularFunctionFieldBar M'` over $\bar{\mathbb{Q}}$ at which the base-changed $j$ has non-negative order, and whose $R_0$-residue lies in the valuation subring of the place $s$, the image of $f$ in `fieldBar q M'` lies in $O^{\mathrm{SS}}(s)$, and moreover for every $a \in A$ whose residue equals the value at $s$ of the $R_0$-residue of $f$, the difference of $f$ and $a$ lies in $O^{\mathrm{SS}}(s)$ and in its maximal ideal; `hSS_fix`, that each $O^{\mathrm{SS}}(s)$ is stable under preimage along `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$; and `hSS_tr`, that each $O^{\mathrm{SS}}(s)$ contains an element $t$ such that for every $a \in A$ the difference of $t$ and $a$ lies in $O^{\mathrm{SS}}(s)$ and is a unit there.
--
--   The descent data are: a subfield $K_0$ of $\bar{\mathbb{Q}}$ with $\bar{\mathbb{Q}}$ algebraic over $K_0$ and $\pi \in K_0$; a Henselian discrete valuation domain $A_0$ together with an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\bar{\mathbb{Q}}$ is exactly $A \cap K_0$ (`hιK₀`), such that the residue map of $A$ composed with $\iota$ is surjective (`hres`); a generator $\varpi_0$ of the maximal ideal of $A_0$ with $\iota(\varpi_0) = \pi$; a subfield $F_0$ of `fieldBar q M'` characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that the image in `fieldBar q M'` of the base-changed $j$ lies in $F_0$; and an $A_0$-algebra structure on $F_0$ which, by `hj₀`, is given by $\iota$ followed by the inclusion of constants $\bar{\mathbb{Q}} \to$ `fieldBar q M'`.
--
--   The model is a scheme $X_0$ with a morphism $f_0 :$ `X₀ ⟶ Spec A₀` which is integral as a scheme, and proper, flat and locally of finite presentation over $A_0$, all of whose stalks are integrally closed (`hn₀`, normality); an isomorphism $\varphi_0$ of $F_0$ with the function field of $X_0$ compatible with the structure map on $A_0$ (`hφ₀`); and the relative dimension one hypothesis `hdim`: if $\eta$ lies over the closed point of $A_0$ and is not closed (some $z \neq \eta$ is a specialisation of $\eta$), then every $y \neq \eta$ which is a specialisation of $\eta$ is a closed point. For $x \in X_0$, `SemistableModel.localRing X₀ φ₀ x` denotes the subring of $F_0$ obtained by transporting the image of the stalk at $x$ in the function field back along $\varphi_0$. A component dictionary `gen` on $\mathbb{P}^1(\mathbb{Z}/q) \sqcup W$ is given, with: `hgenIg`, the traced local ring at `gen (Sum.inl ℓ)` consists of the elements of $F_0$ lying in $O^{\mathrm{Ig}}(\ell)$; `hgenSS`, the traced local ring at `gen (Sum.inr s)` consists of the elements of $F_0$ lying in $O^{\mathrm{SS}}(s)$; `hgen₀`, every `gen i` lies over the closed point of $A_0$; and `hgen`, a point over the closed point is of the form `gen i` if and only if it is not closed.
--
--   Fixing a point $\ell$ of the projective line $\mathbb{P}^1(\mathbb{Z}/q)$, the conclusion is a conjunction of three assertions.
--
--   First, the generic point `gen (Sum.inl ℓ)` of the Igusa component indexed by $\ell$ lies in the smooth locus of $f_0$.
--
--   Secondly, for every $x_0 \in X_0$ lying over the closed point of $A_0$ which is closed (every specialisation of $x_0$ equals $x_0$), which is a specialisation of `gen (Sum.inl ℓ)` and which lies on no supersingular component (for no $s \in W$ is $x_0$ a specialisation of `gen (Sum.inr s)`), there exist an $A_0$-subalgebra $B$ of $F_0$ and a maximal ideal $\mathfrak{m}$ of $B$ such that: $B$ is finitely generated; $B$ is integrally closed in $F_0$, every element of $F_0$ integral over $B$ lying in $B$; every element of $F_0$ is a ratio $b/c$ with $b, c \in B$ and $c \neq 0$; every prime $\mathfrak{q}$ of $B$ containing the ideal generated by the image of the maximal ideal of $A_0$ and not maximal is a minimal prime of that ideal; every nonzero prime $\mathfrak{p}$ of $B$ not containing the image of the maximal ideal of $A_0$ gives rise to a valuation subring $V$ of $F_0$ whose elements are exactly the $b/c$ with $b, c \in B$ and $c \notin \mathfrak{p}$; for every non-closed point $\eta$ over the closed point of $A_0$ with $B$ contained in the traced local ring at $\eta$, there is a prime $\mathfrak{q}$ of $B$ such that the traced local ring at $\eta$ consists exactly of the $b/c$ with $c \notin \mathfrak{q}$; conversely, for every minimal prime $\mathfrak{q}$ of the ideal generated by the image of the maximal ideal of $A_0$ there is a non-closed point $\eta$ over the closed point whose traced local ring is the corresponding localisation of $B$; if $B$ is contained in the traced local ring at `gen i` for some index $i$, then $i =$ `Sum.inl ℓ`; the traced local ring at $x_0$ consists exactly of the elements $b/c$ of $F_0$ with $b, c \in B$ and $c \notin \mathfrak{m}$; the element of $F_0$ given by the base-changed $j$ via `hjF₀`, or its inverse, lies in the traced local ring at $x_0$; and the structure homomorphism from $A_0$ to the localisation of $B$ at $\mathfrak{m}$ is formally smooth.
--
--   Thirdly, crossings with the supersingular components are unique: for every $s \in W$ and all $x_0, x_1 \in X_0$ which are closed points in the sense that every specialisation of each equals itself, and which are both specialisations of `gen (Sum.inl ℓ)` and of `gen (Sum.inr s)`, one has $x_0 = x_1$.
--
--   This is the local analysis, in the case $q = 3$ at an auxiliary level rigidified by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the Igusa components of a normal proper flat model over the descent base $A_0$ of the full-level modular curve: each such component is smooth over the base, its closed points away from the supersingular components lie in finitely generated normal affine charts that are formally smooth over $A_0$ and meet that component only, and each supersingular component crosses it in at most one point. It is used in the construction of the semistable scheme over the descent base attached to the given families of valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_three_of_dvd
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
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

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))

    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))
    (φ₀ : ↥F₀ ≃+* X₀.functionField)
    (hφ₀ : ∀ a : A₀, φ₀ (algebraMap A₀ ↥F₀ a) = SemistableModel.baseToFunctionField toBase₀ a)
    (hdim : ∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
      ∀ z : X₀, y ⤳ z → z = y)

    (gen : CuspidalType.ProjLine q ⊕ ↥W → X₀)
    (hgenIg : ∀ ℓ (f : ↥F₀), f ∈ SemistableModel.localRing X₀ φ₀ (gen (Sum.inl ℓ)) ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ)
    (hgenSS : ∀ s (f : ↥F₀), f ∈ SemistableModel.localRing X₀ φ₀ (gen (Sum.inr s)) ↔ (f : ↥(fieldBar q M')) ∈ OSS s)
    (hgen₀ : ∀ i, toBase₀.base (gen i) = closedPoint A₀)
    (hgen : ∀ x : X₀, toBase₀.base x = closedPoint A₀ → ((∃ i, x = gen i) ↔ ∃ y : X₀, x ⤳ y ∧ y ≠ x))
    (ℓ : CuspidalType.ProjLine q) :

    gen (Sum.inl ℓ) ∈ toBase₀.smoothLocus ∧

    (∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → (∀ y : X₀, x₀ ⤳ y → y = x₀) →
      gen (Sum.inl ℓ) ⤳ x₀ → (∀ s : ↥W, ¬ gen (Sum.inr s) ⤳ x₀) →
      ∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal),

        B.FG ∧
        (∀ x : ↥F₀, _root_.IsIntegral ↥B x → x ∈ B) ∧
        (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
        (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
          𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧

        (∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
          ∃ V : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧
        (∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
          (B : Set ↥F₀) ⊆ SemistableModel.localRing X₀ φ₀ η →
            ∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔
              ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
        (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
          ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
            ∀ x : ↥F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

        (∀ i, (B : Set ↥F₀) ⊆ SemistableModel.localRing X₀ φ₀ (gen i) → i = Sum.inl ℓ) ∧

        (∀ f : ↥F₀, f ∈ SemistableModel.localRing X₀ φ₀ x₀ ↔ ∃ b c : ↥B, c ∉ 𝔪 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

        ((⟨_, hjF₀⟩ : ↥F₀) ∈ SemistableModel.localRing X₀ φ₀ x₀ ∨ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ ∈ SemistableModel.localRing X₀ φ₀ x₀) ∧

        (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) ∧

    (∀ (s : ↥W) (x₀ x₁ : X₀), (∀ y : X₀, x₀ ⤳ y → y = x₀) → (∀ y : X₀, x₁ ⤳ y → y = x₁) →
      gen (Sum.inl ℓ) ⤳ x₀ → gen (Sum.inr s) ⤳ x₀ → gen (Sum.inl ℓ) ⤳ x₁ → gen (Sum.inr s) ⤳ x₁ → x₀ = x₁) := by sorry
