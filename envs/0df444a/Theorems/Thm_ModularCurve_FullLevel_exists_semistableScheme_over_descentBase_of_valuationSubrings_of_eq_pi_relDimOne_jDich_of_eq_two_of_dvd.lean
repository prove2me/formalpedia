-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/2a26d241-c626-5a40-94ac-dd621006b54f
-- title:
--   Semistable descent model at q=2 with Igusa–Drinfeld components
-- statement:
--   Throughout, $q$ is a prime with $q = 2$, $M'$ is a nonzero natural number not divisible by $q$, and $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ dividing $M'$. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ is a nonunit of $A$.
--
--   *Reduction data.* $W$ is a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ (a place being a valuation subring, proper and a principal ideal ring, containing the base field), and `hW` says that $W$ consists exactly of the supersingular places `ssPlaces q M' (ResidueField A)`: the rational places $w$ (those for which $\mathrm{ResidueField}\,A$ surjects onto the residue field of $w$) satisfying `IsAffineGeomPlace` and with $w.\mathrm{evalAt}$ of `jGeomGen` lying in `ssJSet q`. Here $\mathrm{modularFunctionFieldC}\,k\,N$ is the subfield of $k\{\!\{t\}\!\}$ generated over $k$ by the $q$-expansions `jqModC k` and `jqNModC k N`. The hypothesis `hle` is the inclusion $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ of intermediate fields of $\overline{\mathbb{Q}}\{\!\{t\}\!\}$ over $\overline{\mathbb{Q}}$, where the first is the $\overline{\mathbb{Q}}$-base change of the full level-$M'$ modular function field and the second is the $\overline{\mathbb{Q}}$-base change of the $X_H$ function field at level $q^2M'$ with $H = \mathrm{levelH}\,q\,M'$. Next, $R_0$ is a `ConstantReduction` of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$: a valuation subring $R_0.\mathrm{integers}$, a surjective ring homomorphism $R_0.\mathrm{residue}$ from it onto the target with kernel its maximal ideal, inducing on constants the residue map of $A$, together with a degree-preserving map on places compatible with the divisor of a function with nonzero residue, and such that every nonzero function becomes residually nonzero after scaling by a constant. The hypothesis `hR₀` requires that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is the coefficientwise reduction of $y$ modulo the maximal ideal of $A$.
--
--   *Uniformiser and root of unity.* $\pi \in \overline{\mathbb{Q}}$ satisfies $\pi^{q^2-1} = q$ and $\pi \in A$; $\zeta$ is an element of `Idx q`, that is, a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$.
--
--   *The two families of charts.* $O^{\mathrm{Ig}}$ assigns a valuation subring of $\mathrm{fieldBar}\,q\,M'$ to each point of $\mathbb{P}^1(\mathbb{Z}/q)$ ([`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21)), and $O^{\mathrm{SS}}$ assigns one to each element of $W$.
--
--   The Igusa group of hypotheses is: `hIg_inf`, which says that $f$ lies in $O^{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$, the chart at $[1:0]$, if and only if $f$ is a quotient $x/y$ of Laurent series with coefficients in $A$ with $y$ having nonzero reduction; `hIg`, which says that for each point $L$ of $\mathbb{P}^1(\mathbb{Z}/q)$ (the binder of `hIg` shadows the prime $\ell$) there is $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` carries $[1:0]$ to $L$ and for which $O^{\mathrm{Ig}}(L)$ is the preimage of $O^{\mathrm{Ig}}([1:0])$ under the automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ (the automorphism characterised by `IsLevelAutBar`, the $q$-expansion condition normalised by $\zeta \mapsto e^{2\pi i/q}$, and the identity if no such automorphism exists); `hIg_inj`, injectivity of $O^{\mathrm{Ig}}$; and `hIg_perm`, which says that for every $\zeta'$ in `Idx q` and every $\gamma \in \Gamma_0(M')$ the preimages under $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permute the family $O^{\mathrm{Ig}}$.
--
--   The supersingular group is: `hSS_A`, which says that for each $s \in W$ a constant $x \in \overline{\mathbb{Q}}$ lies in $O^{\mathrm{SS}}(s)$ if and only if $x \in A$; `hSS_over`, which says that if $f \in \mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$, if $f$ has nonnegative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb{Q}}$ at which the element $\hat\jmath = \mathrm{coeffEmb}\,\overline{\mathbb{Q}}\,\mathrm{jq}$ (the $j$-expansion, viewed in $\mathrm{modularFunctionFieldBar}\,M'$) has nonnegative order, and if the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ under the inclusion given by `hle` lies in $O^{\mathrm{SS}}(s)$, and moreover for every $a \in A$ whose residue in $\mathrm{ResidueField}\,A$ equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of that image and the constant $a$ lies in the maximal ideal of $O^{\mathrm{SS}}(s)$; `hSS_fix`, which says that each $O^{\mathrm{SS}}(s)$ is preserved by the preimage under $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$; and `hSS_tr`, which provides for each $s \in W$ an element $t \in O^{\mathrm{SS}}(s)$ such that $t - a$ is a unit of $O^{\mathrm{SS}}(s)$ for every $a \in A$.
--
--   *The descent base.* $K_0$ is a subfield of $\overline{\mathbb{Q}}$ with $\overline{\mathbb{Q}}$ algebraic over $K_0$ and $\pi \in K_0$; $A_0$ is a henselian discrete valuation ring (a domain, local, with the stated algebraic structure), $\iota : A_0 \to A$ is an injective local ring homomorphism whose image in $\overline{\mathbb{Q}}$ is exactly $A \cap K_0$ as a set (`hιK₀`), such that the composite of $\iota$ with the residue map of $A$ is surjective (`hres`), and $\varpi_0 \in A_0$ generates the maximal ideal of $A_0$ with $\iota(\varpi_0) = \pi$ in $\overline{\mathbb{Q}}$.
--
--   **Conclusion.** There exist a scheme $X_0$ in universe $0$, a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ which is proper, flat and locally of finite presentation with $X_0$ integral, a subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ over which $\mathrm{fieldBar}\,q\,M'$ is algebraic, and a ring isomorphism $\varphi_0 : F_0 \to X_0.\mathrm{functionField}$, such that all of the following hold.
--
--   1.
--
--   $F_0$ is the set of $f \in \mathrm{fieldBar}\,q\,M'$ all of whose Laurent coefficients (indexed by $n \in \mathbb{Z}$) lie in $K_0$.
--
--   2.
--
--   For every $a \in A_0$ such that the constant $\iota(a)$ lies in $F_0$, $\varphi_0$ of that element equals $\mathrm{SemistableModel.baseToFunctionField}\,\mathrm{toBase}_0\,a$, the germ at the generic point of the pullback of $a$.
--
--   3.
--
--   Every stalk of $X_0$ is integrally closed.
--
--   4.
--
--   The map sending $a \in A_0$ to the image of $a$ in the global sections of $X_0$ (via the inverse of `Scheme.ΓSpecIso` and $\mathrm{toBase}_0$ on global sections) is bijective.
--
--   5.
--
--   Every point $y$ of $X_0$ lying over the generic point of $\operatorname{Spec} A_0$ (prime ideal $\bot$) lies in the smooth locus of $\mathrm{toBase}_0$.
--
--   6.
--
--   (Relative dimension one.) If $\eta$ lies over the closed point of $\operatorname{Spec} A_0$ and admits a specialisation distinct from itself, and if $y$ is a specialisation of $\eta$ with $y \neq \eta$, then $y$ is closed, i.e. every specialisation of $y$ equals $y$.
--
--   7.
--
--   ($j$-dichotomy.) Assuming that the image of $\hat\jmath$ in $\mathrm{fieldBar}\,q\,M'$ under the inclusion given by `hle` lies in $F_0$: for every point $x_0$ of $X_0$ lying over the closed point of $\operatorname{Spec} A_0$ and closed in $X_0$, either that element or its inverse lies in $\mathrm{SemistableModel.localRing}\,X_0\,\varphi_0\,x_0$, the subring of $F_0$ obtained as the image of the stalk at $x_0$ inside the function field, transported by $\varphi_0^{-1}$.
--
--   8.
--
--   (Tame nodes.) For every $x_0$ lying over the closed point of $\operatorname{Spec} A_0$ and not in the smooth locus of $\mathrm{toBase}_0$: the stalk at $x_0$ is a Noetherian ring, and there is a natural number $w \ge 1$ with $w$ a unit in $A_0$, together with a ring isomorphism
--   $$e : \widehat{\mathcal{O}}_{X_0,x_0} \;\xrightarrow{\ \sim\ }\; \widehat{A_0}[\![X_0,X_1]\!]/(X_0X_1 - \varpi_0^{\,w}),$$
--   where the source is the adic completion of the stalk with respect to its maximal ideal, $\widehat{A_0}$ is the adic completion of $A_0$ at its maximal ideal and the two variables are indexed by `Fin 2`, such that for every $a \in A_0$ the image under $e$ of the germ at $x_0$ of the global section attached to $a$ is the class of the constant multivariate power series $C$ of the image of $a$ in $\widehat{A_0}$.
--
--   9.
--
--   (Component and node dictionary.) There are maps $\mathrm{gen} : \mathbb{P}^1(\mathbb{Z}/q) \sqcup W \to X_0$ and $\mathrm{nd} : \mathbb{P}^1(\mathbb{Z}/q) \times W \to X_0$, both injective, with:
--    * for every point $L$ of $\mathbb{P}^1(\mathbb{Z}/q)$ and every $f \in F_0$: $f$ lies in $\mathrm{SemistableModel.localRing}\,X_0\,\varphi_0\,(\mathrm{gen}(\mathrm{inl}\,L))$ if and only if $f$ lies in $O^{\mathrm{Ig}}(L)$;
--    * for every $s \in W$ and every $f \in F_0$: $f$ lies in $\mathrm{SemistableModel.localRing}\,X_0\,\varphi_0\,(\mathrm{gen}(\mathrm{inr}\,s))$ if and only if $f$ lies in $O^{\mathrm{SS}}(s)$;
--    * every $\mathrm{gen}(i)$ lies over the closed point of $\operatorname{Spec} A_0$;
--    * a point $x$ lying over the closed point of $\operatorname{Spec} A_0$ is of the form $\mathrm{gen}(i)$ if and only if it admits a specialisation distinct from itself;
--    * every $\mathrm{nd}(e)$ is closed: each of its specialisations equals it;
--    * for $e = (L,s)$ and any index $i$: $\mathrm{nd}(e)$ is a specialisation of $\mathrm{gen}(i)$ if and only if $i = \mathrm{inl}\,L$ or $i = \mathrm{inr}\,s$;
--    * no $\mathrm{nd}(e)$ lies in the smooth locus of $\mathrm{toBase}_0$;
--    * every point distinct from all $\mathrm{nd}(e)$ lies in the smooth locus of $\mathrm{toBase}_0$;
--    * every point $x$ lying over the closed point of $\operatorname{Spec} A_0$ which is closed and distinct from all $\mathrm{nd}(e)$ is a specialisation of $\mathrm{gen}(i)$ for exactly one index $i$.
--
--   This is the existence of a normal, proper, flat Stein model over the henselian discrete valuation ring $A_0$ realising $A \cap K_0$ of the full level-$q^2M'$ modular curve, with smooth generic fibre and a special fibre whose non-closed points are the Igusa components indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and the supersingular (Drinfeld) components indexed by the supersingular places $W$, crossing in tame ordinary double points indexed by the product; the charts are recorded by the valuation subrings $O^{\mathrm{Ig}}$ and $O^{\mathrm{SS}}$ of the function field. It is the case $q = 2$ at a rigid auxiliary level, the guard $\ell \equiv 11 \pmod{12}$, $\ell \mid M'$ being what makes the node widths units, and it is cited by [`ModularCurve.FullLevel.exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_two_of_dvd
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

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π) :
    ∃ (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
      (_ : IsIntegral X₀) (_ : IsProper toBase₀) (_ : Flat toBase₀) (_ : LocallyOfFinitePresentation toBase₀)
      (F₀ : Subfield ↥(fieldBar q M')) (_ : Algebra.IsAlgebraic ↥F₀ ↥(fieldBar q M'))
      (φ₀ : ↥F₀ ≃+* X₀.functionField),

      (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀) ∧

      (∀ (a : A₀) (h : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) ∈ F₀),
        φ₀ ⟨_, h⟩ = SemistableModel.baseToFunctionField toBase₀ a) ∧

      (∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y)) ∧
      Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)) ∧
      (∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus) ∧

      (∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
        ∀ z : X₀, y ⤳ z → z = y) ∧

      (∀ (hj : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀) (x₀ : X₀),
        toBase₀.base x₀ = closedPoint A₀ → (∀ y : X₀, x₀ ⤳ y → y = x₀) →
          (⟨_, hj⟩ : ↥F₀) ∈ SemistableModel.localRing X₀ φ₀ x₀ ∨ (⟨_, hj⟩ : ↥F₀)⁻¹ ∈ SemistableModel.localRing X₀ φ₀ x₀) ∧

      (∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → x₀ ∉ toBase₀.smoothLocus →
        IsNoetherianRing (X₀.presheaf.stalk x₀) ∧
        ∃ (w : ℕ), 1 ≤ w ∧ IsUnit ((w : ℕ) : A₀) ∧

          ∃ e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
              (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀) ⧸
                Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀)) * MvPowerSeries.X 1 -
                  MvPowerSeries.C ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)}),
            ∀ a : A₀,
              e (algebraMap (X₀.presheaf.stalk x₀) _
                  ((X₀.presheaf.germ ⊤ x₀ trivial).hom
                    (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
                Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))) ∧

      (∃ (gen : CuspidalType.ProjLine q ⊕ ↥W → X₀) (nd : CuspidalType.ProjLine q × ↥W → X₀),
        Function.Injective gen ∧ Function.Injective nd ∧

        (∀ ℓ (f : ↥F₀), f ∈ SemistableModel.localRing X₀ φ₀ (gen (Sum.inl ℓ)) ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ) ∧
        (∀ s (f : ↥F₀), f ∈ SemistableModel.localRing X₀ φ₀ (gen (Sum.inr s)) ↔ (f : ↥(fieldBar q M')) ∈ OSS s) ∧
        (∀ i, toBase₀.base (gen i) = closedPoint A₀) ∧

        (∀ x : X₀, toBase₀.base x = closedPoint A₀ → ((∃ i, x = gen i) ↔ ∃ y : X₀, x ⤳ y ∧ y ≠ x)) ∧

        (∀ e : CuspidalType.ProjLine q × ↥W, ∀ y : X₀, nd e ⤳ y → y = nd e) ∧
        (∀ (e : CuspidalType.ProjLine q × ↥W) (i : CuspidalType.ProjLine q ⊕ ↥W),
          gen i ⤳ nd e ↔ (i = Sum.inl e.1 ∨ i = Sum.inr e.2)) ∧
        (∀ e, nd e ∉ toBase₀.smoothLocus) ∧

        (∀ x : X₀, (∀ e, x ≠ nd e) → x ∈ toBase₀.smoothLocus) ∧
        (∀ x : X₀, toBase₀.base x = closedPoint A₀ → (∀ y : X₀, x ⤳ y → y = x) → (∀ e, x ≠ nd e) →
          ∃! i, gen i ⤳ x)) := by sorry
