-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_drinfeldChart_localRing_eq_localization_formallySmooth_of_normalModel_gen_j
-- name    : ModularCurve.FullLevel.exists_drinfeldChart_localRing_eq_localization_formallySmooth_of_normalModel_gen_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/59fd6050-ad35-5882-9871-023e1137ad5f
-- title:
--   Smoothness and Drinfeld affine charts of the descended model
-- statement:
--   Throughout, $q$ is a prime with $q\ge 5$, $M'$ is a nonzero natural number not divisible by $q$, and $A$ is a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime q`, i.e. $q$ lies in the nonunits of $A$. Two function fields intervene: `modularFunctionFieldBar M'`, the intermediate field of $\overline{\mathbb Q}((t))$ obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images of the full-level modular function field `modularFunctionFieldFull M'`, and `fieldBar q M'`, the corresponding base change to $\overline{\mathbb Q}$ of the level-$H$ function field at level $q^2M'$ for the subgroup `levelH q M'` of $(\mathbb Z/q^2M')^\times$; the hypothesis `hle` asserts the inclusion of the former in the latter. Further, $W$ is a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$, and `hW` says that $W$ consists exactly of the members of `ssPlaces q M' (ResidueField A)`, i.e. of the places $w$ that are rational, satisfy `IsAffineGeomPlace`, and whose value $w$`.evalAt (jGeomGen _ M')` lies in `ssJSet q`. The datum `R₀` is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'`: a valuation subring `R₀.integers` together with a surjective residue homomorphism `R₀.residue` onto the latter field whose kernel is the maximal ideal, compatible with $A$ and with its residue map, admitting scaling of any nonzero element into the integers with nonzero residue, and a map `R₀.placeMap` on places preserving degrees and compatible with pushforward of divisors. The hypothesis `hR₀` requires this reduction to compute coefficientwise reduction of Laurent series: for every Laurent series $y$ over $A$ whose image in $\overline{\mathbb Q}((t))$ lies in `modularFunctionFieldBar M'`, that image lies in `R₀.integers` and its `R₀`-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$. Finally $\pi\in A$ satisfies $\pi^{q^2-1}=q$ in $\overline{\mathbb Q}$, and $\zeta$ is an element of `Idx q`, that is a primitive $q$-th root of unity in $\overline{\mathbb Q}$.
--
--   The geometry of the special fibre is presented by two families of valuation subrings of `fieldBar q M'`: the Igusa family `OIg`, indexed by the projective line $\mathbb P^1(\mathbb Z/q)$, and the supersingular (Drinfeld) family `OSS`, indexed by $W$. Four hypotheses govern `OIg`: `hIg_inf` describes the ring at the point `lineInfty q` $=[1:0]$ as those $f$ admitting Laurent series $x,y$ over $A$ with $y$ of nonzero coefficientwise reduction and $f\cdot y=x$ after coefficient extension to $\overline{\mathbb Q}$; `hIg` provides, for each $\ell$, a matrix $\gamma\in\Gamma_0(M')$ whose reduction `redQ q γ` carries `lineInfty q` to $\ell$ and for which `OIg ℓ` is the preimage of `OIg (lineInfty q)` under `levelAutBar q M' ζ γ`; `hIg_inj` asserts injectivity of `OIg`; and `hIg_perm` asserts that for every primitive root $\zeta'$ and every $\gamma\in\Gamma_0(M')$ the automorphism `levelAutBar q M' ζ' γ` permutes the family `OIg` along a permutation of $\mathbb P^1(\mathbb Z/q)$. Four hypotheses govern `OSS`: `hSS_A` says that an element of $\overline{\mathbb Q}$ lies in `OSS s` if and only if it lies in $A$; `hSS_over` relates `OSS s` to the place $s$ through `R₀`, namely for $f$ in `modularFunctionFieldBar M'` lying in `R₀.integers`, if $f$ has nonnegative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the element $\hat j$ (the coefficientwise image of the $q$-expansion `jq` of the modular invariant) has nonnegative order, and if the `R₀`-residue of $f$ lies in the valuation subring of $s$, then the image of $f$ in `fieldBar q M'` lies in `OSS s`, and moreover for every $a\in A$ whose residue equals $s$`.evalAt` of that `R₀`-residue, the difference of the image of $f$ and $a$ lies in the maximal ideal of `OSS s`; `hSS_fix` says each `OSS s` is stable under pullback along every `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$; and `hSS_tr` provides for each $s$ an element $t\in$ `OSS s` such that $t-a$ is a unit of `OSS s` for every $a\in A$.
--
--   The descent data are: a subfield $K_0$ of $\overline{\mathbb Q}$ over which $\overline{\mathbb Q}$ is algebraic and which contains $\pi$; a henselian discrete valuation ring $A_0$ (a domain) with an injective local ring homomorphism $\iota\colon A_0\to A$ whose image in $\overline{\mathbb Q}$ is exactly $A\cap K_0$ (`hιK₀`), such that the composite of $\iota$ with the residue map of $A$ is surjective (`hres`), together with a generator $\varpi_0$ of the maximal ideal of $A_0$ (`hϖ₀`) satisfying $\iota(\varpi_0)=\pi$ (`hϖ₀π`); a subfield $F_0$ of `fieldBar q M'` characterised by `hF₀` as consisting of those elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that $\hat j$, viewed in `fieldBar q M'`, lies in $F_0$; and an $A_0$-algebra structure on $F_0$ which by `hj₀` is the one induced by $\iota$.
--
--   The model is an integral scheme $X_0$ with a proper, flat morphism `toBase₀` to $\operatorname{Spec} A_0$ that is locally of finite presentation, all of whose stalks are integrally closed (`hn₀`), equipped with a ring isomorphism $\varphi_0$ from $F_0$ onto the function field of $X_0$ compatible with the $A_0$-structures (`hφ₀`), and satisfying the relative-dimension-one condition `hdim`: if $\eta$ lies over the closed point of $A_0$ and is not closed, then any point $y\ne\eta$ in the closure of $\eta$ is closed. The dictionary of special components is a map `gen` from $\mathbb P^1(\mathbb Z/q)\sqcup W$ to $X_0$ such that the trace on $F_0$ of the local ring at `gen (Sum.inl ℓ)` consists of the elements of `OIg ℓ` (`hgenIg`) and that at `gen (Sum.inr s)` of the elements of `OSS s` (`hgenSS`), all points `gen i` lie over the closed point of $A_0$ (`hgen₀`), and a point over the closed point is of the form `gen i` precisely when it is not closed in $X_0$ (`hgen`). Here the local ring at a point means `SemistableModel.localRing X₀ φ₀`, the image in $F_0$ of the stalk at that point under the canonical map into the function field transported by $\varphi_0^{-1}$.
--
--   For a fixed $s\in W$ the conclusion has two parts. First, `gen (Sum.inr s)` lies in the smooth locus of `toBase₀`.
--
--   Second, for every point $x_0$ of $X_0$ lying over the closed point of $A_0$, closed in $X_0$ (every $y$ in the closure of $x_0$ equals $x_0$), lying in the closure of `gen (Sum.inr s)` and in the closure of no `gen (Sum.inl ℓ)`, there exist an $A_0$-subalgebra $B$ of $F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that: $B$ is a finitely generated $A_0$-algebra; $B$ is integrally closed in $F_0$, every element of $F_0$ integral over $B$ lying in $B$; $F_0$ is the field of fractions of $B$, in the sense that every $x\in F_0$ satisfies $xc=b$ for some $b,c\in B$ with $c\ne0$; every prime ideal of $B$ containing the ideal generated by the image of the maximal ideal of $A_0$ and not maximal is a minimal prime over that ideal; for every nonzero prime $\mathfrak p$ of $B$ not containing that ideal there is a valuation subring $V$ of $F_0$ consisting exactly of the fractions $b/c$ with $b,c\in B$ and $c\notin\mathfrak p$; for every non-closed point $\eta$ over the closed point of $A_0$ with $B$ contained in the local ring of $X_0$ at $\eta$, there is a prime $\mathfrak q$ of $B$ such that this local ring is precisely the set of such fractions with denominators outside $\mathfrak q$; conversely every minimal prime $\mathfrak q$ over the image of the maximal ideal of $A_0$ arises from some non-closed point $\eta$ over the closed point in this way; the element $\hat j$ of $F_0$ lies in $B$; for every index $i$, if $B$ is contained in the local ring at `gen i` then $i=$ `Sum.inr s`; the local ring at $x_0$ consists exactly of the fractions $b/c$ with $b,c\in B$ and $c\notin\mathfrak m$; and the structure map from $A_0$ to the localisation of $B$ at $\mathfrak m$ is formally smooth.
--
--   This is the Drinfeld-component step in the construction of the descended semistable model of the full-level modular curve: the generic point of the supersingular component attached to $s$ is a smooth point of the model over the descent base, and every closed point of that component lying on no Igusa component admits a normal affine $A_0$-chart, containing the $j$-invariant, which meets that component only and whose local ring at the corresponding maximal ideal is formally smooth over $A_0$. It feeds the assembly of the semistable scheme over the descent base from the given families of valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_drinfeldChart_localRing_eq_localization_formallySmooth_of_normalModel_gen_j.lean

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

theorem ModularCurve.FullLevel.exists_drinfeldChart_localRing_eq_localization_formallySmooth_of_normalModel_gen_j
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
    (s : ↥W) :

    gen (Sum.inr s) ∈ toBase₀.smoothLocus ∧

    (∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → (∀ y : X₀, x₀ ⤳ y → y = x₀) →
      gen (Sum.inr s) ⤳ x₀ → (∀ ℓ : CuspidalType.ProjLine q, ¬ gen (Sum.inl ℓ) ⤳ x₀) →
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

        (⟨_, hjF₀⟩ : ↥F₀) ∈ B ∧

        (∀ i, (B : Set ↥F₀) ⊆ SemistableModel.localRing X₀ φ₀ (gen i) → i = Sum.inr s) ∧

        (∀ f : ↥F₀, f ∈ SemistableModel.localRing X₀ φ₀ x₀ ↔ ∃ b c : ↥B, c ∉ 𝔪 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

        (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) := by sorry
