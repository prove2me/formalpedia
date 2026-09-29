-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/9ba6edb0-e257-5a8f-8176-96a47562b3ed
-- title:
--   Smooth Igusa charts and unique crossings, q=2
-- statement:
--   Throughout, $q$ is a prime with $q=2$, and $M'$ is a non-zero natural number not divisible by $q$. A prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ is fixed as a guard (the letter $\ell$ is re-used at the very end of the binder list for a point of $\mathbb{P}^1(\mathbb{Z}/q)$).
--
--   **The residue data.** $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ lies in the non-units of $A$. $W$ is a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over $\mathrm{ResidueField}\,A$ (a place being a valuation subring containing the base field, proper and with principal ideals), and `hW` says that $W$ consists exactly of the supersingular places: those $w$ that are rational, are affine geometric places, and have $w.\mathrm{evalAt}$ of the geometric $j$-generator in the supersingular $j$-set for $q$. The hypothesis `hle` asserts the inclusion $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ of the Laurent base change of the full level-$M'$ modular function field into the function field of level $q^2M'$ with the subgroup $\mathrm{levelH}\,q\,M' = \ker(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. $R_0$ is a `ConstantReduction` of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$: a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto the target with kernel the maximal ideal, a map on places preserving degrees and compatible with divisors, and compatibility with the structure map of $A$. The hypothesis `hR₀` states that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\mathrm{ResidueField}\,A$, is the coefficientwise reduction of $y$.
--
--   **Uniformiser and root of unity.** $\pi \in \overline{\mathbb{Q}}$ satisfies $\pi^{q^2-1} = q$ and $\pi \in A$; $\zeta$ is an element of $\mathrm{Idx}\,q$, the set of primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$.
--
--   **The charts.** $O_{\mathrm{Ig}}$ assigns a valuation subring of $\mathrm{fieldBar}\,q\,M'$ to each point of $\mathbb{P}^1(\mathbb{Z}/q)$ and $O_{\mathrm{SS}}$ one to each $s \in W$. Four hypotheses govern $O_{\mathrm{Ig}}$: `hIg_inf` describes $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ as the set of $f$ whose Laurent expansion can be written as a quotient $x/y$ of coefficientwise images of Laurent series over $A$ with the reduction of $y$ non-zero; `hIg` provides, for each line, some $\gamma \in \Gamma_0(M')$ with $\mathrm{redQ}\,q\,\gamma \cdot \mathrm{lineInfty}\,q$ equal to that line and $O_{\mathrm{Ig}}$ of it equal to the pullback of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; `hIg_inj` asserts injectivity of $O_{\mathrm{Ig}}$; `hIg_perm` asserts that for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pullbacks along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permute the family $O_{\mathrm{Ig}}$. Four hypotheses govern $O_{\mathrm{SS}}$: `hSS_A` says a constant lies in $O_{\mathrm{SS}}(s)$ exactly when it lies in $A$; `hSS_over` says that if $f \in R_0.\mathrm{integers}$ has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the element $j = \mathrm{coeffEmb}\,\overline{\mathbb{Q}}\,\mathrm{jq}$ has non-negative order, and the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{SS}}(s)$ and, for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that residue, the difference $f - a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$; `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is stable under pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for all $\zeta'$ and $\gamma \in \Gamma_0(M')$; `hSS_tr` provides for each $s$ an element $t \in O_{\mathrm{SS}}(s)$ such that $t - a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a \in A$.
--
--   **The descent data.** $K_0$ is a subfield of $\overline{\mathbb{Q}}$ with $\overline{\mathbb{Q}}$ algebraic over it and $\pi \in K_0$. $A_0$ is a Henselian discrete valuation ring which is a domain, and $\iota : A_0 \to A$ is an injective local ring homomorphism whose image in $\overline{\mathbb{Q}}$ is exactly $A \cap K_0$ (`hιK₀`), such that the composite $A_0 \to \mathrm{ResidueField}\,A$ is surjective (`hres`); $\varpi_0$ generates the maximal ideal of $A_0$ and $\iota(\varpi_0) = \pi$ in $\overline{\mathbb{Q}}$. $F_0$ is a subfield of $\mathrm{fieldBar}\,q\,M'$ characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; `hjF₀` states that $j$, viewed in $\mathrm{fieldBar}\,q\,M'$ via `hle`, lies in $F_0$. $F_0$ carries an $A_0$-algebra structure whose structure map is, by `hj₀`, the composite of $\iota$ with $\overline{\mathbb{Q}} \to \mathrm{fieldBar}\,q\,M'$.
--
--   **The model and its component dictionary.** $X_0$ is a scheme with a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ which is integral (as a scheme), proper, flat and locally of finite presentation, all stalks of $X_0$ being integrally closed (`hn₀`); $\varphi_0 : F_0 \cong X_0.\mathrm{functionField}$ is a ring isomorphism compatible with the structure maps, i.e. $\varphi_0 \circ (\text{algebraMap } A_0\,F_0) = \mathrm{baseToFunctionField}\,\mathrm{toBase}_0$ (`hφ₀`). The relative-dimension-one hypothesis `hdim` states that if $\eta$ lies over the closed point of $A_0$ and is not closed (admits a strict specialisation), and $\eta \rightsquigarrow y$ with $y \ne \eta$, then $y$ is closed. For $x \in X_0$, $\mathrm{SemistableModel.localRing}\,X_0\,\varphi_0\,x$ denotes the trace on $F_0$ of the local ring at $x$, namely the image of the stalk in the function field transported by $\varphi_0^{-1}$. The dictionary $\mathrm{gen} : \mathbb{P}^1(\mathbb{Z}/q) \oplus W \to X_0$ satisfies: the traced local ring at $\mathrm{gen}(\mathrm{inl}\,\ell')$ consists of the $f \in F_0$ lying in $O_{\mathrm{Ig}}(\ell')$ (`hgenIg`) and at $\mathrm{gen}(\mathrm{inr}\,s)$ of the $f \in F_0$ lying in $O_{\mathrm{SS}}(s)$ (`hgenSS`); all $\mathrm{gen}\,i$ lie over the closed point of $A_0$ (`hgen₀`); and a point over the closed point is of the form $\mathrm{gen}\,i$ precisely when it is not closed (`hgen`).
--
--   Finally, $\ell$ denotes a point of $\mathbb{P}^1(\mathbb{Z}/q)$.
--
--   **Conclusion.** Three assertions hold.
--
--   (i) $\mathrm{gen}(\mathrm{inl}\,\ell)$ lies in the smooth locus of $\mathrm{toBase}_0$.
--
--   (ii) For every $x_0 \in X_0$ lying over the closed point of $A_0$, closed in $X_0$ (every $y$ with $x_0 \rightsquigarrow y$ equals $x_0$), with $\mathrm{gen}(\mathrm{inl}\,\ell) \rightsquigarrow x_0$ and with $\mathrm{gen}(\mathrm{inr}\,s) \not\rightsquigarrow x_0$ for every $s \in W$, there exist an $A_0$-subalgebra $B$ of $F_0$ and a maximal ideal $\mathfrak{m}$ of $B$ such that: $B$ is a finitely generated $A_0$-algebra; $B$ is integrally closed in $F_0$ (every $x \in F_0$ integral over $B$ lies in $B$); every $x \in F_0$ is a quotient $b/c$ with $b, c \in B$, $c \ne 0$; every prime $\mathfrak{q}$ of $B$ containing the image ideal $\mathfrak{m}_{A_0}B = \mathrm{Ideal.map}(\text{algebraMap } A_0\,B)(\mathrm{maximalIdeal}\,A_0)$ and not maximal is a minimal prime over $\mathfrak{m}_{A_0}B$; for every non-zero prime $\mathfrak{p}$ of $B$ not containing $\mathfrak{m}_{A_0}B$ there is a valuation subring $V$ of $F_0$ whose elements are exactly the $f$ with $f\,c = b$ for some $b \in B$ and $c \in B \setminus \mathfrak{p}$, i.e. the localisation $B_{\mathfrak{p}}$ is a valuation ring; for every non-closed $\eta$ over the closed point of $A_0$ with $B \subseteq \mathrm{SemistableModel.localRing}\,X_0\,\varphi_0\,\eta$ there is a prime $\mathfrak{q}$ of $B$ with that traced local ring equal to $B_{\mathfrak{q}}$; conversely, for every minimal prime $\mathfrak{q}$ over $\mathfrak{m}_{A_0}B$ there is a non-closed $\eta$ over the closed point whose traced local ring is $B_{\mathfrak{q}}$; for every index $i$, the inclusion $B \subseteq \mathrm{SemistableModel.localRing}\,X_0\,\varphi_0\,(\mathrm{gen}\,i)$ forces $i = \mathrm{inl}\,\ell$; the traced local ring at $x_0$ is $B_{\mathfrak{m}}$; either $j$ or $j^{-1}$ (as an element of $F_0$ via `hjF₀`) lies in the traced local ring at $x_0$; and the structure map $A_0 \to \mathrm{Localization.AtPrime}\,\mathfrak{m}$ is formally smooth.
--
--   (iii) For every $s \in W$ and all $x_0, x_1 \in X_0$ that are closed in $X_0$ and satisfy $\mathrm{gen}(\mathrm{inl}\,\ell) \rightsquigarrow x_0$, $\mathrm{gen}(\mathrm{inr}\,s) \rightsquigarrow x_0$, $\mathrm{gen}(\mathrm{inl}\,\ell) \rightsquigarrow x_1$ and $\mathrm{gen}(\mathrm{inr}\,s) \rightsquigarrow x_1$, one has $x_0 = x_1$: the Igusa component indexed by $\ell$ and the component indexed by $s$ cross in at most one closed point.
--
--   This is the $q = 2$ instance, under the rigidifying guard provided by an auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the local study of the descended full-level modular curve along an Igusa component: reducedness of the component, affine formally smooth charts around its closed points away from the supersingular components, and uniqueness of each crossing. It feeds the construction of the semistable scheme over the descent base carried out in [`ModularCurve.FullLevel.exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_two_of_dvd
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
