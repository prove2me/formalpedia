-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_nodeChart_point_specializes_iff_adicCompletion_stalk_of_normalModel_gen_j_local_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_nodeChart_point_specializes_iff_adicCompletion_stalk_of_normalModel_gen_j_local_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/d29ff7fb-b8dc-5f7b-9c4a-968a40bb584a
-- title:
--   Node chart at (ℓ,s) of the descended full-level model, q=3
-- statement:
--   Throughout, $q$ is a prime with $q=3$, and $M'$ is a nonzero natural number not divisible by $q$. A further auxiliary prime is fixed: a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ (the hypotheses `hℓ`, `hℓ12`, `hℓM'`); the last binder of the theorem introduces a point of $\mathbb{P}^1(\mathbb{Z}/q)$ which in the Lean text is also written `ℓ`, shadowing the prime, and is referred to below as the line $\ell$.
--
--   *Base valuation ring and level data.* $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ lies in the non-units of $A$. $W$ is a finite set of places of `modularFunctionFieldC (ResidueField A) M'` — the intermediate field of $\mathrm{Laurent}(\kappa)$, $\kappa$ the residue field of $A$, generated over $\kappa$ by `jqModC` and `jqNModC … M'` — over $\kappa$, and `hW` says that $W$ consists exactly of the supersingular places, i.e. of the places $w$ that are rational (the structure map $\kappa \to w$'s residue field is surjective), satisfy `IsAffineGeomPlace`, and have `w.evalAt (jGeomGen …)` in `ssJSet q`. Here a place is a valuation subring of the ambient field, containing the base field, proper, and a principal ideal ring, and `ord`, `evalAt` are its normalised order function and residual evaluation. The hypothesis `hle` asserts the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'` of intermediate fields of $\mathrm{Laurent}(\overline{\mathbb{Q}})$ over $\overline{\mathbb{Q}}$: the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $M'$ sits inside the base change `fieldBar q M'` of the $X_H$-function field of level $q^2M'$, $H$ being the kernel `levelH q M'` of the relevant reduction map of unit groups.
--
--   *Constant reduction.* $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'`: a valuation subring `R₀.integers`, a surjective residue homomorphism onto the target with kernel the maximal ideal, a map on places, and the usual compatibilities (constants reduce to constants, scaling into the integers with nonzero residue, preservation of degrees and of divisor push-forward). The hypothesis `hR₀` pins $R_0$ down coefficientwise: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that element lies in `R₀.integers` and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$.
--
--   *Uniformiser and root of unity.* $\pi \in \overline{\mathbb{Q}}$ satisfies $\pi^{q^2-1} = q$ and $\pi \in A$; $\zeta$ is an element of `Idx q`, the set of primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$, used to index the level automorphisms `levelAutBar q M' ζ γ` of `fieldBar q M'` over $\overline{\mathbb{Q}}$ (the automorphism characterised by the $q$-expansion condition `IsLevelAutBar`, the identity if none exists).
--
--   *The two families of charts.* $O^{\mathrm{Ig}}$ assigns to each point of $\mathbb{P}^1(\mathbb{Z}/q)$, and $O^{\mathrm{SS}}$ to each $s \in W$, a valuation subring of `fieldBar q M'`. Four hypotheses govern the Igusa family: `hIg_inf` identifies $O^{\mathrm{Ig}}$ at the point `lineInfty q` as the set of $f$ expressible as a ratio $x/y$ of Laurent series with coefficients in $A$ with the reduction of $y$ nonzero; `hIg` provides, for each line, a $\gamma \in \Gamma_0(M')$ whose reduction carries `lineInfty q` to that line and for which the chart is the pullback of the chart at infinity along `levelAutBar q M' ζ γ`; `hIg_inj` asserts injectivity of $O^{\mathrm{Ig}}$; `hIg_perm` asserts that for any $\zeta'$ and any $\gamma \in \Gamma_0(M')$ the pullback along `levelAutBar q M' ζ' γ` permutes the family. Four hypotheses govern the supersingular family: `hSS_A` says a constant from $\overline{\mathbb{Q}}$ lies in $O^{\mathrm{SS}}_s$ exactly when it lies in $A$; `hSS_over` says that if $f \in$ `R₀.integers` has no pole at any place of `modularFunctionFieldBar M'` where $j$ (the element of `modularFunctionFieldBar M'` given by the coefficientwise image of `jq`) has none, and if the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in `fieldBar q M'` lies in $O^{\mathrm{SS}}_s$, and for every $a \in A$ whose residue equals $s$'s evaluation of that $R_0$-residue, the difference $f - a$ lies in the maximal ideal of $O^{\mathrm{SS}}_s$; `hSS_fix` says each $O^{\mathrm{SS}}_s$ is invariant under pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; `hSS_tr` provides for each $s$ an element $t \in O^{\mathrm{SS}}_s$ with $t - a$ a unit of $O^{\mathrm{SS}}_s$ for every $a \in A$.
--
--   *Descent data.* $K_0$ is a subfield of $\overline{\mathbb{Q}}$ with $\overline{\mathbb{Q}}$ algebraic over it and $\pi \in K_0$; $A_0$ is a Henselian discrete valuation domain with an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb{Q}}$ is exactly $A \cap K_0$ (`hιK₀`), such that the composite of $\iota$ with the residue map of $A$ is surjective (`hres`); $\varpi_0$ generates the maximal ideal of $A_0$ and $\iota(\varpi_0) = \pi$ in $\overline{\mathbb{Q}}$.
--
--   *Descended function field.* $F_0$ is a subfield of `fieldBar q M'` characterised by `hF₀`: $f \in F_0$ if and only if every Laurent coefficient of $f$ lies in $K_0$. The hypothesis `hjF₀` says the image of $j$ in `fieldBar q M'` lies in $F_0$. An $A_0$-algebra structure on $F_0$ is fixed, and `hj₀` says its structure map sends $a$ to the image of $\iota(a)$ under $\overline{\mathbb{Q}} \to$ `fieldBar q M'`.
--
--   *The model.* $X_0$ is a scheme with a morphism `toBase₀` to $\operatorname{Spec} A_0$ which is integral as a scheme, and proper, flat and locally of finite presentation over $A_0$; `hn₀` says every stalk of $X_0$ is integrally closed; $\varphi_0 : F_0 \cong K(X_0)$ is a ring isomorphism with the function field, compatible with the $A_0$-structures via `SemistableModel.baseToFunctionField` (`hφ₀`); `hdim` is a relative-dimension-one condition: if $\eta$ lies over the closed point of $A_0$ and is not closed, then any $y \neq \eta$ with $\eta \rightsquigarrow y$ is a closed point. Finally `gen` assigns to each $i \in \mathbb{P}^1(\mathbb{Z}/q) \sqcup W$ a point of $X_0$ whose local ring traced on $F_0$ — that is, `SemistableModel.localRing X₀ φ₀`, the image in $F_0$ of the stalk inside the function field — is cut out by the chart: $O^{\mathrm{Ig}}_\ell \cap F_0$ for $i = \mathrm{inl}\,\ell$ (`hgenIg`) and $O^{\mathrm{SS}}_s \cap F_0$ for $i = \mathrm{inr}\,s$ (`hgenSS`); all $\mathrm{gen}\,i$ lie over the closed point of $A_0$ (`hgen₀`), and among the points over the closed point the points of the form $\mathrm{gen}\,i$ are exactly the non-closed ones (`hgen`).
--
--   *Conclusion.* For the fixed pair consisting of a line $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$ and a supersingular place $s \in W$, there exist an $A_0$-subalgebra $B \subseteq F_0$, a maximal ideal $\mathfrak{m}$ of $B$, and a point $x_0 \in X_0$ such that all of the following hold.
--
--   (i) $B$ is a finitely generated $A_0$-algebra.
--
--   (ii) Every $x \in F_0$ integral over `SemistableModel.localRing X₀ φ₀ x₀` belongs to that ring.
--
--   (iii) Every $x \in F_0$ can be written as $x = b/c$ with $b, c \in B$, $c \neq 0$; i.e. $B$ has fraction field $F_0$.
--
--   (iv) Every prime $\mathfrak{q}$ of $B$ which contains the ideal generated by the image of the maximal ideal of $A_0$ and which is not maximal is a minimal prime of that ideal.
--
--   (v) For every $\eta \in X_0$ lying over the closed point of $A_0$ and not closed, with $B$ contained in `SemistableModel.localRing X₀ φ₀ η`, there is a prime $\mathfrak{q}$ of $B$ such that the traced local ring at $\eta$ consists exactly of the elements $b/c$ with $b, c \in B$, $c \notin \mathfrak{q}$.
--
--   (vi) Conversely, for every minimal prime $\mathfrak{q}$ of the image ideal of the maximal ideal of $A_0$ there is a non-closed point $\eta$ of $X_0$ over the closed point of $A_0$ whose traced local ring is the localisation of $B$ at $\mathfrak{q}$ in the same sense.
--
--   (vii) The element of $F_0$ given by $j$ together with `hjF₀` lies in $B$.
--
--   (viii) The image of $\varpi_0$ in $B$ lies in $\mathfrak{m}$.
--
--   (ix) $x_0$ lies over the closed point of $A_0$ and is a closed point of $X_0$ (every $y$ with $x_0 \rightsquigarrow y$ equals $x_0$).
--
--   (x) `SemistableModel.localRing X₀ φ₀ x₀` consists exactly of the elements $b/c$ with $b, c \in B$, $c \notin \mathfrak{m}$.
--
--   (xi) For every $i$, $\mathrm{gen}\,i \rightsquigarrow x_0$ holds if and only if $i = \mathrm{inl}\,\ell$ or $i = \mathrm{inr}\,s$; so exactly the two components indexed by $\ell$ and by $s$ pass through $x_0$.
--
--   (xii) $\mathrm{gen}(\mathrm{inl}\,\ell) \neq \mathrm{gen}(\mathrm{inr}\,s)$.
--
--   (xiii) The structure map $A_0 \to B_{\mathfrak{m}}$, i.e. $A_0 \to$ `Localization.AtPrime 𝔪`, is not formally smooth.
--
--   (xiv) The stalk of $X_0$ at $x_0$ is a Noetherian ring, and there exists $w \geq 1$ with $w$ a unit in $A_0$ and a ring isomorphism
--   $$e : \widehat{\mathcal{O}}_{X_0,x_0} \;\cong\; \widehat{A_0}[[X_0, X_1]]/(X_0X_1 - \varpi_0^{\,w}),$$
--   where the left-hand side is the adic completion of the stalk at its maximal ideal, $\widehat{A_0}$ is the adic completion of $A_0$ at its maximal ideal, the power series ring is `MvPowerSeries (Fin 2)` over $\widehat{A_0}$, and the ideal is generated by $X_0X_1$ minus the constant $(\text{image of } \varpi_0 \text{ in } \widehat{A_0})^w$; moreover $e$ is compatible with the base: for every $a \in A_0$, $e$ sends the image in the completion of the germ at $x_0$ of the pullback of $a$ along `toBase₀` to the class of the constant $a$ in $\widehat{A_0}$.
--
--   This is the node chart of the descended full-level model: around the point where the Igusa component indexed by the line $\ell$ meets the supersingular (Drinfeld) component indexed by $s$, it produces a finitely generated affine $A_0$-chart $B$ with fraction field $F_0$, normal and with localisations computing the traced local rings of the non-closed special points, and identifies the completed local ring at the crossing point $x_0$ with $\widehat{A_0}[[X_0,X_1]]/(X_0X_1 - \varpi_0^w)$ over $\widehat{A_0}$, $w$ invertible in $A_0$; in particular $x_0$ is not formally smooth over the base. It is the case $q = 3$, under the rigidifying hypothesis that some prime $\ell \equiv 11 \pmod{12}$ divides $M'$, and it feeds the Igusa-chart and Drinfeld-chart statements and the assembly of the semistable scheme over the descent base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_nodeChart_point_specializes_iff_adicCompletion_stalk_of_normalModel_gen_j_local_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_nodeChart_point_specializes_iff_adicCompletion_stalk_of_normalModel_gen_j_local_of_eq_three_of_dvd
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
    (ℓ : CuspidalType.ProjLine q) (s : ↥W) :
    ∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal) (x₀ : X₀),

      B.FG ∧

      (∀ x : ↥F₀, _root_.IsIntegral ↥(SemistableModel.localRing X₀ φ₀ x₀) x → x ∈ SemistableModel.localRing X₀ φ₀ x₀) ∧
      (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
        𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
      (∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
        (B : Set ↥F₀) ⊆ SemistableModel.localRing X₀ φ₀ η →
          ∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔
            ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
        ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
          ∀ x : ↥F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

      (⟨_, hjF₀⟩ : ↥F₀) ∈ B ∧

      algebraMap A₀ ↥B ϖ₀ ∈ 𝔪 ∧
      toBase₀.base x₀ = closedPoint A₀ ∧ (∀ y : X₀, x₀ ⤳ y → y = x₀) ∧
      (∀ f : ↥F₀, f ∈ SemistableModel.localRing X₀ φ₀ x₀ ↔ ∃ b c : ↥B, c ∉ 𝔪 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ i, gen i ⤳ x₀ ↔ (i = Sum.inl ℓ ∨ i = Sum.inr s)) ∧
      gen (Sum.inl ℓ) ≠ gen (Sum.inr s) ∧

      ¬ (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth ∧

      (IsNoetherianRing (X₀.presheaf.stalk x₀) ∧
      ∃ (w : ℕ), 1 ≤ w ∧ IsUnit ((w : ℕ) : A₀) ∧

        ∃ e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
            (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀) ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀)) * MvPowerSeries.X 1 -
                MvPowerSeries.C ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)}),
          ∀ a : A₀,
            e (algebraMap (X₀.presheaf.stalk x₀) _
                ((X₀.presheaf.germ ⊤ x₀ trivial).hom
                  (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
              Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))) := by sorry
