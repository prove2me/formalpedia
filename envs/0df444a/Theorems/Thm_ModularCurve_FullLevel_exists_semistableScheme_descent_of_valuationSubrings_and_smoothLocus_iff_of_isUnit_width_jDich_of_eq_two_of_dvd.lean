-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/c9e79d95-3e36-5d8b-93fa-913c7afdcbf1
-- title:
--   Semistable A-model of the full level-2 modular curve
-- statement:
--   Throughout, $\bar{\mathbb Q}$ denotes `AlgebraicClosure ℚ`.
--
--   **Data.** A prime $q$ with $q = 2$; a nonzero natural number $M'$ with $q \nmid M'$; a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$; a valuation subring $A \subseteq \bar{\mathbb Q}$ with `A.LiesOverPrime q`, i.e. $q$ lies in `A.nonunits`; writing $k =$ `ResidueField A`, a finite set $W$ of places of the level-$M'$ modular function field `modularFunctionFieldC k M'` $= k(j, j_{M'})$ over $k$, characterised by `hW` as consisting exactly of the supersingular places in the sense of `ssPlaces q M' k`, namely the places $w$ that are rational, are affine geometric places, and whose value $w.\mathrm{evalAt}$ at the geometric $j$-generator lies in `ssJSet q k`. Further, `hle` asserts the inclusion `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` of intermediate fields of `LaurentSeries` $\bar{\mathbb Q}$ over $\bar{\mathbb Q}$: the $\bar{\mathbb Q}$-base change $\bar F_{M'}$ of the full level-$M'$ modular function field sits inside $F =$ `fieldBar q M'`, the $\bar{\mathbb Q}$-base change of the function field of $X_H$ at level $q^2M'$ for the subgroup $H =$ `levelH q M'` of $(\mathbb Z/q^2M')^\times$ (the kernel of a reduction map of unit groups).
--
--   Next, a constant reduction $R_0$ of $\bar F_{M'}$ relative to $A$ with residue field of constants $k$ and residue function field `modularFunctionFieldC k M'`: that is, a valuation subring `R₀.integers` of $\bar F_{M'}$, a surjective ring map `R₀.residue` from it onto `modularFunctionFieldC k M'` with kernel the maximal ideal, a map `R₀.placeMap` on places preserving degrees, such that a constant $x \in \bar{\mathbb Q}$ lies in `R₀.integers` exactly when $x \in A$, residues of constants are the $A$-residues, every nonzero element can be scaled by a constant into `R₀.integers` so as to have nonzero residue, and divisors of elements with nonzero residue push forward to the divisors of their residues. The hypothesis `hR₀` states that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\bar{\mathbb Q}$ lies in $\bar F_{M'}$, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over $k$, is the coefficientwise reduction of $y$.
--
--   Finally: an element $\pi \in \bar{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$; a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`); and two families of valuation subrings of $F$, namely `OIg` indexed by $\mathbb P^1(\mathbb F_q)$ and `OSS` indexed by $W$.
--
--   **Igusa hypotheses.** `hIg_inf`: $f \in$ `OIg (lineInfty q)` if and only if there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ is nonzero and $f \cdot \bar y = \bar x$ in `LaurentSeries` $\bar{\mathbb Q}$, where $\bar{(\cdot)}$ denotes pushforward along $A \hookrightarrow \bar{\mathbb Q}$. `hIg`: for every point of $\mathbb P^1(\mathbb F_q)$ (the bound variable reuses the name $\ell$) there is $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` carries `lineInfty q` to that point and for which the corresponding ring `OIg` is the pullback of `OIg (lineInfty q)` along the automorphism `levelAutBar q M' ζ γ` of $F$. `hIg_inj`: `OIg` is injective. `hIg_perm`: for every primitive root $\zeta'$ and every $\gamma \in \Gamma_0(M')$, pullback along `levelAutBar q M' ζ' γ` permutes the family `OIg`, through some permutation of $\mathbb P^1(\mathbb F_q)$.
--
--   **Supersingular hypotheses.** `hSS_A`: for each $s \in W$ and $x \in \bar{\mathbb Q}$, the image of $x$ in $F$ lies in `OSS s` if and only if $x \in A$. `hSS_over`: for $s \in W$ and $f \in$ `R₀.integers` such that $f$ has nonnegative order at every place of $\bar F_{M'}$ over $\bar{\mathbb Q}$ at which $j$ (the image under `coeffEmb` of the Laurent expansion `jq`) has nonnegative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$: then the image of $f$ in $F$ under the inclusion `hle` lies in `OSS s`, and moreover for every $a \in A$ whose $A$-residue equals the value at $s$ of the $R_0$-residue of $f$, the difference of that image and $a$ lies in `OSS s` and lies in the maximal ideal of `OSS s`. `hSS_fix`: each `OSS s` is invariant under pullback along `levelAutBar q M' ζ' γ` for every primitive root $\zeta'$ and every $\gamma \in \Gamma_0(M')$. `hSS_tr`: for each $s \in W$ there is $t \in$ `OSS s` such that for every $a \in A$ the difference $t - a$ lies in `OSS s` and is a unit there.
--
--   **Conclusion.** There exist a scheme $X$ (in universe $0$), a morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$ with $X$ integral and $\mathrm{toBase}$ proper, flat and locally of finite presentation, and a ring isomorphism $\varphi : F \xrightarrow{\sim} X.\mathrm{functionField}$, such that the following four assertions hold.
--
--   (i) For every $a \in A$, $\varphi$ carries the image of $a$ in $F$ to `SemistableModel.baseToFunctionField toBase a`; that is, $\varphi$ is compatible with the structure map of $X$ over $A$.
--
--   (ii) Every stalk of $X$ is integrally closed.
--
--   (iii) *(Descent to a henselian discretely valued subbase.)* There exist a subfield $K_0 \subseteq \bar{\mathbb Q}$ with $\bar{\mathbb Q}$ algebraic over $K_0$, a ring $A_0$ that is a domain, a discrete valuation ring and a henselian local ring, a local injective-to-be ring map $\iota : A_0 \to A$, an element $\varpi_0 \in A_0$, a scheme $X_0$ with a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ that is integral, proper, flat and locally of finite presentation, an isomorphism $\mathrm{iso} : X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ (the pullback of $\mathrm{toBase}_0$ along $\operatorname{Spec}$ of $\iota$), a subfield $F_0 \subseteq F$ with $F$ algebraic over $F_0$, and a ring isomorphism $\varphi_0 : F_0 \xrightarrow{\sim} X_0.\mathrm{functionField}$, such that, writing $\mathrm{pr}$ for $\mathrm{iso.hom}$ followed by the first projection of the pullback:
--   $\pi \in K_0$; the maximal ideal of $A_0$ is generated by $\varpi_0$; $\iota$ is injective; the image of $A_0$ in $\bar{\mathbb Q}$ is exactly $A \cap K_0$; the composite of $\iota$ with the residue map of $A$ is surjective; $\mathrm{iso.hom}$ followed by the second projection is $\mathrm{toBase}$; $\mathrm{pr}$ sends the generic point of $X$ to the generic point of $X_0$; for every $s \in F_0$, $\varphi(s)$ equals the image of $\varphi_0(s)$ under the specialisation map of $X_0$ followed by the stalk map of $\mathrm{pr}$ at the generic point of $X$;
--
--   further, a point $x \in X$ lies in the smooth locus of $\mathrm{toBase}$ if and only if $\mathrm{pr}(x)$ lies in the smooth locus of $\mathrm{toBase}_0$;
--
--   and finally, for every point $x_0$ of $X_0$ lying over the closed point of $A_0$ and not in the smooth locus of $\mathrm{toBase}_0$: the stalk of $X_0$ at $x_0$ is a noetherian ring, and there is an integer $w \ge 1$ with $w$ a unit in $A_0$ together with a ring isomorphism
--   $$e : \widehat{\mathcal O_{X_0,x_0}} \xrightarrow{\ \sim\ } \widehat{A_0}[[X_0, X_1]]/(X_0X_1 - \varpi_0^w),$$
--   where the completions are the adic completions with respect to the maximal ideals of the stalk and of $A_0$, such that $e$ carries the image of each $a \in A_0$ (through the structure map of $X_0$ over $A_0$, the germ at $x_0$, and the completion) to the class of the constant power series with coefficient the image of $a$ in $\widehat{A_0}$.
--
--   (iv) *(Dictionary of components and nodes on the special fibre.)* There exist maps $\mathrm{gen} : \mathbb P^1(\mathbb F_q) \sqcup W \to X$ and $\mathrm{nd} : \mathbb P^1(\mathbb F_q) \times W \to X$, both injective, such that:
--   for each point of $\mathbb P^1(\mathbb F_q)$ the subring `SemistableModel.localRing X φ` at the corresponding $\mathrm{gen}$-point (the $\varphi$-preimage of the image of the stalk in the function field) is the underlying subring of the associated `OIg`; for each $s \in W$ the same subring at $\mathrm{gen}(s)$ is the underlying subring of `OSS s`; every $\mathrm{gen}$-point lies over the closed point of $A$; a point $x$ of $X$ over the closed point of $A$ is a $\mathrm{gen}$-point if and only if it specialises to some $y \ne x$; each $\mathrm{nd}(e)$ is a closed point, in the sense that $\mathrm{nd}(e) \rightsquigarrow y$ forces $y = \mathrm{nd}(e)$; for $e = (\lambda, s)$ and any index $i$ of $\mathrm{gen}$, one has $\mathrm{gen}(i) \rightsquigarrow \mathrm{nd}(e)$ if and only if $i$ is $\lambda$ in the left summand or $s$ in the right summand; no $\mathrm{nd}(e)$ lies in the smooth locus of $\mathrm{toBase}$; conversely every point of $X$ that is not of the form $\mathrm{nd}(e)$ lies in the smooth locus; every closed point $x$ over the closed point of $A$ (that is, $x \rightsquigarrow y$ implies $y = x$) which is not any $\mathrm{nd}(e)$ satisfies $\mathrm{gen}(i) \rightsquigarrow x$ for exactly one index $i$; and, for every such closed point $x$ of the special fibre and every $a \in A$, writing $j$ for the image in $F$ (via `hle`) of the Laurent expansion `jq` of the modular invariant, either $j - a$ or $(j - a)^{-1}$ lies in `SemistableModel.localRing X φ x`.
--
--   The existential clauses in (iii) are asserted with $\mathrm{pr}$ spelled out each time, and the compatibility of $\varphi$ with $\varphi_0$ is stated for an arbitrary proof that $\mathrm{pr}$ matches the generic points.
--
--   This is the construction, for $q = 2$ at an auxiliary level rigidified by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the semistable proper flat model over a valuation ring $A$ of $\bar{\mathbb Q}$ above $q$ of the modular curve of full level $q$ over $\Gamma_0(M')$: the components of the special fibre are pinned to the prescribed Igusa and supersingular valuation rings, the nodes are indexed by pairs (line, supersingular place) with tame thickness, and the whole model descends to a henselian discrete valuation subbase. It feeds the assembly of the semistable covering data in [`ModularCurve.FullLevel.SemistableCovering.exists_semistableModel_descent_of_discCharts_of_noCuspFreePackageSS_of_jPins_of_nodeRings_nodeCharts_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.SemistableCovering.exists_semistableModel_descent_of_discCharts_of_noCuspFreePackageSS_of_jPins_of_nodeRings_nodeCharts_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich_of_eq_two_of_dvd
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
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s)) :
    ∃ (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
      (_ : IsIntegral X) (_ : IsProper toBase) (_ : Flat toBase) (_ : LocallyOfFinitePresentation toBase)
      (φ : ↥(fieldBar q M') ≃+* X.functionField),

      (∀ a : ↥A, φ (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ)) =
        SemistableModel.baseToFunctionField toBase a) ∧

      (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) ∧

      (∃ (K₀ : Subfield (AlgebraicClosure ℚ)) (_ : Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ))
          (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀) (_ : HenselianLocalRing A₀)
          (ι : A₀ →+* ↥A) (_ : IsLocalHom ι) (ϖ₀ : A₀)
          (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
          (_ : IsIntegral X₀) (_ : IsProper toBase₀) (_ : Flat toBase₀) (_ : LocallyOfFinitePresentation toBase₀)
          (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
          (F₀ : Subfield ↥(fieldBar q M')) (_ : Algebra.IsAlgebraic ↥F₀ ↥(fieldBar q M'))
          (φ₀ : ↥F₀ ≃+* X₀.functionField),
        π ∈ K₀ ∧ maximalIdeal A₀ = Ideal.span {ϖ₀} ∧
        Function.Injective ι ∧
        Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) = (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)) ∧
        Function.Surjective ((IsLocalRing.residue ↥A).comp ι) ∧
        iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase ∧
        (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint X) = genericPoint X₀ ∧
        (∀ (s : ↥F₀) (hgen : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint X) =
            genericPoint X₀),
          φ (s : ↥(fieldBar q M')) =
            ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint X)).hom
              ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₀ s))) ∧

        (∀ x : X, x ∈ toBase.smoothLocus ↔
          (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x ∈ toBase₀.smoothLocus) ∧

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
                  Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a)))) ∧

      (∃ (gen : CuspidalType.ProjLine q ⊕ ↥W → X) (nd : CuspidalType.ProjLine q × ↥W → X),
        Function.Injective gen ∧ Function.Injective nd ∧
        (∀ ℓ, SemistableModel.localRing X φ (gen (Sum.inl ℓ)) = (OIg ℓ).toSubring) ∧
        (∀ s, SemistableModel.localRing X φ (gen (Sum.inr s)) = (OSS s).toSubring) ∧
        (∀ i, toBase.base (gen i) = closedPoint ↥A) ∧

        (∀ x : X, toBase.base x = closedPoint ↥A → ((∃ i, x = gen i) ↔ ∃ y : X, x ⤳ y ∧ y ≠ x)) ∧

        (∀ e : CuspidalType.ProjLine q × ↥W, ∀ y : X, nd e ⤳ y → y = nd e) ∧
        (∀ (e : CuspidalType.ProjLine q × ↥W) (i : CuspidalType.ProjLine q ⊕ ↥W),
          gen i ⤳ nd e ↔ (i = Sum.inl e.1 ∨ i = Sum.inr e.2)) ∧
        (∀ e, nd e ∉ toBase.smoothLocus) ∧

        (∀ x : X, (∀ e, x ≠ nd e) → x ∈ toBase.smoothLocus) ∧
        (∀ x : X, toBase.base x = closedPoint ↥A → (∀ y : X, x ⤳ y → y = x) → (∀ e, x ≠ nd e) →
          ∃! i, gen i ⤳ x) ∧

        (∀ x : X, toBase.base x = closedPoint ↥A → (∀ y : X, x ⤳ y → y = x) → ∀ a : ↥A,
          (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) -
              algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ) ∈ SemistableModel.localRing X φ x ∨
          ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) -
              algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ))⁻¹ ∈ SemistableModel.localRing X φ x)) := by sorry
