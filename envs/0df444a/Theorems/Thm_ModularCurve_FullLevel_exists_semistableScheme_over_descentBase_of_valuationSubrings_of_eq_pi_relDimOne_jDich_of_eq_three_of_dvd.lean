-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/b7898c9c-8369-50e7-a4a0-6de624817028
-- title:
--   Semistable normal model over a henselian descent base, q=3
-- statement:
--   Throughout, $\bar{\mathbb{Q}}$ denotes `AlgebraicClosure ℚ`, and Laurent series fields over a field are used as the ambient of all function fields: `modularFunctionFieldBar M'` is the subfield of $\bar{\mathbb{Q}}$-Laurent series generated over $\bar{\mathbb{Q}}$ by the image of the full level-$M'$ modular function field `modularFunctionFieldFull M'` (itself generated over $\mathbb{Q}$ by the divisor expansions), `fieldBar q M'` is the analogous $\bar{\mathbb{Q}}$-base change of the function field of the modular curve $X_H$ of level $q^2M'$ with $H =$ `levelH q M'` the kernel of `ZMod.unitsMap (dvd_sq_mul q M')`, and for a field $K$ the field `modularFunctionFieldC K M'` is generated over $K$ by the $q$-expansions of $j$ and of $j$ at level $M'$. A `Place K F` is a valuation subring of $F$, distinct from $F$, containing the image of $K$ and a principal ideal ring, with its order function `ord` and its $K$-valued evaluation `evalAt`.
--
--   Data and arithmetic hypotheses. A prime $q$ with $q = 3$; a non-zero natural number $M'$ with $q \nmid M'$; a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$; a valuation subring $A \subseteq \bar{\mathbb{Q}}$ with `A.LiesOverPrime q`, that is $q$ is a non-unit of $A$; a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over `ResidueField A` whose members are, by `hW`, exactly the elements of `ssPlaces q M' (ResidueField A)` (the rational affine geometric places whose $j$-value is supersingular in characteristic $q$); the inclusion `hle` of `modularFunctionFieldBar M'` in `fieldBar q M'`; a constant reduction $R_0$ of type `ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M')`, i.e. a valuation subring $R_0.\mathrm{integers}$ of `modularFunctionFieldBar M'` with a surjective residue map onto `modularFunctionFieldC (ResidueField A) M'` whose kernel is the maximal ideal, inducing $A$ on constants, together with a degree-preserving map on places compatible with divisors; the hypothesis `hR₀`, which requires that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\bar{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over `ResidueField A`, is the coefficientwise reduction of $y$; an element $\pi \in A$ with $\pi^{q^2-1} = q$; and $\zeta$ an element of `Idx q`, the set of primitive $q$-th roots of unity in $\bar{\mathbb{Q}}$.
--
--   The charts. Two families of valuation subrings of `fieldBar q M'` are given: `OIg` indexed by [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) $= \mathbb{P}^1(\mathbb{Z}/q)$ and `OSS` indexed by $W$. Four hypotheses govern `OIg`: `hIg_inf` says that $f \in$ `OIg (lineInfty q)` holds if and only if there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to `ResidueField A` is non-zero and $f \cdot y = x$ in $\bar{\mathbb{Q}}$-Laurent series; `hIg` says that for every line (the bound variable here reuses the name $\ell$) there is $\gamma \in$ `Gamma0 M'` with `redQ q γ • lineInfty q` equal to that line and `OIg` of it equal to the pullback of `OIg (lineInfty q)` along `levelAutBar q M' ζ γ`; `hIg_inj` says `OIg` is injective; `hIg_perm` says that for every $\zeta'$ in `Idx q` and every $\gamma \in$ `Gamma0 M'` the pullbacks along `levelAutBar q M' ζ' γ` permute the family `OIg`. Four hypotheses govern `OSS`: `hSS_A` says that a constant from $\bar{\mathbb{Q}}$ lies in `OSS s` exactly when it lies in $A$; `hSS_over` says that for $s \in W$ and $f \in R_0.\mathrm{integers}$ which has non-negative order at every place of `modularFunctionFieldBar M'` over $\bar{\mathbb{Q}}$ at which the element $\hat{\jmath} =$ `coeffEmb (AlgebraicClosure ℚ) jq` has non-negative order, and whose $R_0$-residue lies in the valuation subring of the place $s$, the image of $f$ in `fieldBar q M'` lies in `OSS s`, and moreover for every $a \in A$ whose residue equals `s.evalAt` of that $R_0$-residue the difference of this image and the constant $a$ lies in the maximal ideal of `OSS s`; `hSS_fix` says each `OSS s` is invariant under pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in$ `Gamma0 M'`; `hSS_tr` says each `OSS s` contains an element $t$ such that $t - a$ is a unit of `OSS s` for every $a \in A$.
--
--   The descent base. A subfield $K_0 \subseteq \bar{\mathbb{Q}}$ with $\bar{\mathbb{Q}}$ algebraic over $K_0$ and $\pi \in K_0$; a commutative domain $A_0$ which is a henselian discrete valuation ring; an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\bar{\mathbb{Q}}$ is exactly $A \cap K_0$ (`hιK₀`) and which induces a surjection onto `ResidueField A` (`hres`); a generator $\varpi_0$ of the maximal ideal of $A_0$ with $\iota(\varpi_0) = \pi$ in $\bar{\mathbb{Q}}$ (`hϖ₀π`).
--
--   Conclusion. There exist a scheme $X_0$, a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ together with witnesses that $X_0$ is integral and that $\mathrm{toBase}_0$ is proper, flat and locally of finite presentation, a subfield $F_0$ of `fieldBar q M'` such that `fieldBar q M'` is algebraic over $F_0$, and a ring isomorphism $\varphi_0 : F_0 \xrightarrow{\sim} X_0.\mathrm{functionField}$, satisfying the following nine conjuncts.
--
--   (1) For $f \in$ `fieldBar q M'`: $f \in F_0$ if and only if every Laurent coefficient of $f$, at every index $n \in \mathbb{Z}$, lies in $K_0$.
--
--   (2) For every $a \in A_0$ such that the constant $\iota(a) \in \bar{\mathbb{Q}}$, viewed in `fieldBar q M'`, lies in $F_0$, the image of that element under $\varphi_0$ equals `SemistableModel.baseToFunctionField toBase₀ a`, i.e. the germ at the generic point of the pullback of $a$ under $\mathrm{toBase}_0$.
--
--   (3) Every stalk of $X_0$ is integrally closed.
--
--   (4) The map $a \mapsto$ `toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)` from $A_0$ to the global sections of $X_0$ is bijective.
--
--   (5) Every point $y$ of $X_0$ lying over the zero ideal of $A_0$ belongs to `toBase₀.smoothLocus`.
--
--   (6) Relative dimension one in the special fibre: if $\eta$ lies over the closed point of $A_0$ and is non-closed (it specialises to some $z \neq \eta$), and $y \neq \eta$ is a specialisation of $\eta$, then $y$ is closed, i.e. every $z$ with $y \rightsquigarrow z$ equals $y$.
--
--   (7) A $j$-dichotomy, conditional on the hypothesis `hj` that the image in `fieldBar q M'` of the element $\hat{\jmath} =$ `coeffEmb (AlgebraicClosure ℚ) jq` of `modularFunctionFieldBar M'` lies in $F_0$: for every $x_0$ lying over the closed point of $A_0$ and closed in $X_0$, either $\hat{\jmath}$ or its inverse lies in `SemistableModel.localRing X₀ φ₀ x₀`, the subring of $F_0$ obtained as the image under $\varphi_0^{-1}$ of the stalk at $x_0$ inside the function field.
--
--   (8) Local structure at non-smooth closed special points: for every $x_0$ lying over the closed point of $A_0$ and not in `toBase₀.smoothLocus`, the stalk at $x_0$ is a Noetherian ring, and there exists a natural number $w \ge 1$ with $w$ a unit of $A_0$ together with a ring isomorphism
--   $$e : \widehat{\mathcal{O}_{X_0,x_0}} \xrightarrow{\sim} \hat{A_0}[[X_0,X_1]] / (X_0X_1 - \varpi_0^{\,w}),$$
--   where the completions are the adic completions at the respective maximal ideals and $\varpi_0^{\,w}$ is taken as a constant power series over $\hat{A_0}$, such that for every $a \in A_0$ the image under $e$ of the completion of the germ at $x_0$ of the pullback of $a$ is the class of the constant power series of $a$.
--
--   (9) The component and node dictionary: there exist maps `gen` from $\mathbb{P}^1(\mathbb{Z}/q) \sqcup W$ to $X_0$ and `nd` from $\mathbb{P}^1(\mathbb{Z}/q) \times W$ to $X_0$, both injective, such that for every line $\ell$ and every $f \in F_0$ one has $f \in$ `SemistableModel.localRing X₀ φ₀ (gen (Sum.inl ℓ))` if and only if $f \in$ `OIg ℓ`; for every $s \in W$ and every $f \in F_0$ one has $f \in$ `SemistableModel.localRing X₀ φ₀ (gen (Sum.inr s))` if and only if $f \in$ `OSS s`; every point in the image of `gen` lies over the closed point of $A_0$; a point $x$ over the closed point of $A_0$ is in the image of `gen` precisely when it is non-closed; each $\mathrm{nd}\,e$ is a closed point of $X_0$; for $e$ and an index $i$ one has $\mathrm{gen}\,i \rightsquigarrow \mathrm{nd}\,e$ if and only if $i =$ `Sum.inl e.1` or $i =$ `Sum.inr e.2`; no $\mathrm{nd}\,e$ lies in `toBase₀.smoothLocus`; every point of $X_0$ different from all $\mathrm{nd}\,e$ lies in `toBase₀.smoothLocus`; and every closed point $x$ over the closed point of $A_0$ which is different from all $\mathrm{nd}\,e$ satisfies $\exists!\, i$ with $\mathrm{gen}\,i \rightsquigarrow x$.
--
--   This is the construction, for $q = 3$ at a rigid auxiliary level (a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$), of a normal proper flat model with semistable special fibre of the full-level-$q$ modular curve over the henselian discrete valuation ring $A_0$ whose fraction field is cut out inside $\bar{\mathbb{Q}}$ by the descent field $K_0$, before base change to $A$: the special fibre consists of the Igusa components indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and the supersingular components indexed by $W$, crossing at the nodes indexed by pairs, with each node ordinary double of thickness invertible in $A_0$. It is used by [`ModularCurve.FullLevel.exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_semistableScheme_over_descentBase_of_valuationSubrings_of_eq_pi_relDimOne_jDich_of_eq_three_of_dvd
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
