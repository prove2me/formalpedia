-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j
-- name    : ModularCurve.FullLevel.exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/6fca3990-e6e4-57cc-94ef-751ea24e1d65
-- title:
--   Smooth Igusa charts on the descended full-level model
-- statement:
--   Throughout, $q\ge 5$ is a prime, $M'$ is a nonzero natural number not divisible by $q$, and $A$ is a valuation subring of $\bar{\mathbb Q}=$ `AlgebraicClosure ℚ` with $q$ a non-unit of $A$ (the predicate `A.LiesOverPrime q`). The field `modularFunctionFieldBar M'` is the base change to $\bar{\mathbb Q}$ of the full level-$M'$ modular function field, and `fieldBar q M'` is the base change to $\bar{\mathbb Q}$ of the function field of $X_H$ of level $q^2M'$ with $H=$ `levelH q M'`, the kernel of the indicated reduction map of unit groups; `hle` is the inclusion of the first in the second. A finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$ is assumed, by `hW`, to consist exactly of the supersingular places `ssPlaces q M' (ResidueField A)`, i.e. the rational places satisfying `IsAffineGeomPlace` whose value at `jGeomGen` lies in `ssJSet q`. Further data: a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $A$ with residue field `modularFunctionFieldC (ResidueField A) M'` (a valuation subring `R₀.integers` lying over $A$, a surjective residue map with kernel the maximal ideal, compatible with the residue map of $A$, together with its map on places, compatible with degrees and with pushforward of divisors), the hypothesis `hR₀` that every Laurent series $y$ with coefficients in $A$ whose pushforward to $\bar{\mathbb Q}$ lies in `modularFunctionFieldBar M'` belongs to `R₀.integers` and has $R_0$-residue given by the coefficientwise residue of $y$; an element $\pi\in A$ with $\pi^{q^2-1}=q$; an index $\zeta$ of a primitive $q$-th root of unity; and two families of valuation subrings of `fieldBar q M'`, the Igusa charts $O_{\mathrm{Ig}}$ indexed by $\mathbb P^1(\mathbb Z/q)=$ [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) and the supersingular charts $O_{\mathrm{SS}}$ indexed by $W$.
--
--   The Igusa family is constrained by four hypotheses. `hIg_inf` describes the chart at the line `lineInfty q`: an $f$ lies in $O_{\mathrm{Ig}}(\infty)$ precisely when there are Laurent series $x,y$ with coefficients in $A$ such that the coefficientwise residue of $y$ is nonzero and $f\cdot y=x$ after pushing $x,y$ into Laurent series over $\bar{\mathbb Q}$. `hIg` requires that each $\ell$ be reached from `lineInfty q` by some $\gamma\in\Gamma_0(M')$, in the sense that `redQ q γ • lineInfty q = ℓ` and $O_{\mathrm{Ig}}(\ell)$ is the preimage of $O_{\mathrm{Ig}}(\infty)$ under the automorphism `levelAutBar q M' ζ γ`. `hIg_inj` asserts injectivity of $O_{\mathrm{Ig}}$, and `hIg_perm` that for every index $\zeta'$ and every $\gamma\in\Gamma_0(M')$ the family $O_{\mathrm{Ig}}$ is permuted by pullback along `levelAutBar q M' ζ' γ`.
--
--   The supersingular family is constrained by four hypotheses as well. `hSS_A` says that a constant $x\in\bar{\mathbb Q}$ lies in $O_{\mathrm{SS}}(s)$ if and only if $x\in A$. `hSS_over` (a three-clause implication, summarised here) says that if $f\in R_0.\mathrm{integers}$ has non-negative order at every place of `modularFunctionFieldBar M'` at which the $j$-element `coeffEmb jq` has non-negative order, and if the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in `fieldBar q M'` lies in $O_{\mathrm{SS}}(s)$, and for every $a\in A$ whose residue equals the value at $s$ of that $R_0$-residue, the difference between the image of $f$ and the constant $a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$. `hSS_fix` asserts that each $O_{\mathrm{SS}}(s)$ is invariant under pullback along `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma\in\Gamma_0(M')$. `hSS_tr` provides, for each $s$, an element $t\in O_{\mathrm{SS}}(s)$ such that $t-a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a\in A$.
--
--   The descent data are: a subfield $K_0\subseteq\bar{\mathbb Q}$ with $\bar{\mathbb Q}$ algebraic over $K_0$ and $\pi\in K_0$; a henselian discrete valuation domain $A_0$ with an injective local ring homomorphism $\iota:A_0\to A$ whose image, viewed inside $\bar{\mathbb Q}$, is exactly $A\cap K_0$ (`hιK₀`), such that the composite of $\iota$ with the residue map of $A$ is surjective (`hres`); a generator $\varpi_0$ of the maximal ideal of $A_0$ (`hϖ₀`) with $\iota(\varpi_0)=\pi$ (`hϖ₀π`); a subfield $F_0$ of `fieldBar q M'` characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that the image in `fieldBar q M'` of the $j$-element `coeffEmb jq` lies in $F_0$; and an $A_0$-algebra structure on $F_0$ pinned down by `hj₀` to be the one induced by $\iota$ followed by the inclusion of constants.
--
--   The model data are: a scheme $X_0$ with a morphism $\mathrm{toBase}_0:X_0\to\operatorname{Spec}A_0$ which is integral as a scheme, proper, flat and locally of finite presentation, with all stalks integrally closed (`hn₀`); an isomorphism $\varphi_0:F_0\xrightarrow{\sim}$ `X₀.functionField` compatible with the structure map from $A_0$ (`hφ₀`); and the relative-dimension-one hypothesis `hdim`: if $\eta$ lies in the special fibre and is not closed (it has a proper specialisation), and $\eta\rightsquigarrow y$ with $y\ne\eta$, then $y$ is a closed point. Here, for a point $x$, `SemistableModel.localRing X₀ φ₀ x` denotes the subring of $F_0$ obtained by transporting the image of the stalk at $x$ inside the function field along $\varphi_0^{-1}$. The component dictionary is a map $\mathrm{gen}$ from $\mathbb P^1(\mathbb Z/q)\sqcup W$ to $X_0$ with: `hgenIg`, the traced local ring at $\mathrm{gen}(\mathrm{inl}\,\ell)$ is the set of $f\in F_0$ lying in $O_{\mathrm{Ig}}(\ell)$; `hgenSS`, the traced local ring at $\mathrm{gen}(\mathrm{inr}\,s)$ is the set of $f\in F_0$ lying in $O_{\mathrm{SS}}(s)$; `hgen₀`, every $\mathrm{gen}(i)$ lies over the closed point of $\operatorname{Spec}A_0$; and `hgen`, a point of the special fibre is of the form $\mathrm{gen}(i)$ if and only if it admits a proper specialisation. Finally $\ell\in\mathbb P^1(\mathbb Z/q)$ is fixed.
--
--   The conclusion is a conjunction of three assertions.
--
--   First, $\mathrm{gen}(\mathrm{inl}\,\ell)$ lies in the smooth locus of $\mathrm{toBase}_0$.
--
--   Second, for every point $x_0$ of $X_0$ lying over the closed point of $\operatorname{Spec}A_0$, which is closed (every specialisation of $x_0$ equals $x_0$), which is a specialisation of $\mathrm{gen}(\mathrm{inl}\,\ell)$ and is a specialisation of no $\mathrm{gen}(\mathrm{inr}\,s)$, $s\in W$, there exist an $A_0$-subalgebra $B$ of $F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that: $B$ is a finitely generated $A_0$-algebra; $B$ is integrally closed in $F_0$ (every element of $F_0$ integral over $B$ lies in $B$); every element of $F_0$ is a quotient $b/c$ with $b,c\in B$, $c\ne 0$; every prime $\mathfrak q$ of $B$ containing the image of the maximal ideal of $A_0$ and not maximal is a minimal prime over that image; for every nonzero prime $\mathfrak p$ of $B$ not containing the image of the maximal ideal of $A_0$ there is a valuation subring $V$ of $F_0$ consisting exactly of the elements of the form $b/c$ with $b,c\in B$ and $c\notin\mathfrak p$; for every non-closed point $\eta$ of the special fibre (one admitting a proper specialisation) whose traced local ring contains $B$ there is a prime $\mathfrak q$ of $B$ with the traced local ring at $\eta$ equal to the localisation of $B$ at $\mathfrak q$, described as the set of $b/c$ with $c\notin\mathfrak q$; conversely, for every minimal prime $\mathfrak q$ over the image of the maximal ideal of $A_0$ there is such a non-closed point $\eta$ of the special fibre whose traced local ring is that localisation; among the points $\mathrm{gen}(i)$, the only one whose traced local ring contains $B$ is $\mathrm{gen}(\mathrm{inl}\,\ell)$; the traced local ring at $x_0$ is the localisation of $B$ at $\mathfrak m$, in the same explicit form; the element of $F_0$ given by `hjF₀`, or its inverse, lies in the traced local ring at $x_0$; and the structure map from $A_0$ to the localisation `Localization.AtPrime 𝔪` is formally smooth.
--
--   Third, for every $s\in W$ and all points $x_0,x_1$ of $X_0$ that are closed (each specialisation of $x_i$ equals $x_i$) and are simultaneously specialisations of $\mathrm{gen}(\mathrm{inl}\,\ell)$ and of $\mathrm{gen}(\mathrm{inr}\,s)$, one has $x_0=x_1$; that is, the Igusa component $\ell$ and each supersingular component meet in at most one point.
--
--   This is the local analysis of the Igusa components on a normal proper flat model over the descent base $A_0$ of the full level-$q^2M'$ modular curve: the generic point of the component indexed by $\ell$ is smooth over $A_0$, each closed point of that component away from the supersingular (Drinfeld) components sits in a finitely generated, integrally closed affine chart with $A_0$-formally smooth local ring at which $\hat\jmath$ or $\hat\jmath^{-1}$ is regular, and the component crosses each supersingular component at most once. It feeds the construction of the semistable model over the descent base in [`ModularCurve.FullLevel.exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich`](thm.html#ModularCurve.FullLevel.exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j.lean

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

theorem ModularCurve.FullLevel.exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j
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
