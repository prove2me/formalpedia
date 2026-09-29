-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent
-- name    : ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/84c2ff66-cb89-5361-8565-4f7b9507474e
-- title:
--   Formally smooth chart package at a smooth non-supersingular centre
-- statement:
--   Fix a prime $q$ with $5 \le q$ and a level $M'$ (nonzero) with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$, i.e. $q$ is a non-unit of $A$ (`hA`). Let $W$ be a finite set of places of the function field $\mathrm{modularFunctionFieldC}(\kappa_A, M')$ over the residue field $\kappa_A =$ `ResidueField A`, where by `hW` a place $w$ belongs to $W$ exactly when it is supersingular in the sense of `ssPlaces`: $w$ is rational, is an affine geometric place, and the value of the geometric $j$-invariant at $w$ lies in the supersingular set `ssJSet q`. Let `hle` be the inclusion of the base-changed full modular function field $\overline{F}(M') =$ `modularFunctionFieldBar M'` into the base-changed $X_H$-function field $\overline{F}_{q,M'} =$ `fieldBar q M'` at level $q^2M'$ with $H$ the kernel of the reduction map on units. Let $R_0$ be a `ConstantReduction` for $A$ from $\overline{F}(M')$ to $\mathrm{modularFunctionFieldC}(\kappa_A,M')$: a valuation subring $R_0.\mathrm{integers}$ of $\overline{F}(M')$ together with a surjective residue homomorphism onto the characteristic-$p$ function field whose kernel is the maximal ideal, a map on places, and the compatibility clauses of that structure (membership of constants matching $A$, compatibility of the residue map with constants, an existence-of-scaling clause, preservation of degrees of places and compatibility of divisor push-forward with orders). The hypothesis `hR₀` requires that any Laurent series $y$ with coefficients in $A$ whose image in $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ lies in $\overline{F}(M')$ belongs to $R_0.\mathrm{integers}$ and that its $R_0$-residue is the coefficientwise reduction of $y$ modulo the maximal ideal of $A$.
--
--   Further data: an element $\pi \in \overline{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$; an index $\zeta$ of a primitive $q$-th root of unity; a family $O_{\mathrm{Ig}}$ of valuation subrings of $\overline{F}_{q,M'}$ indexed by $\mathbb P^1(\mathbb Z/q)$, and a family $O_{\mathrm{SS}}$ of valuation subrings of $\overline{F}_{q,M'}$ indexed by $W$.
--
--   The Igusa clauses are: `hIg_inf`, which says that $f \in O_{\mathrm{Ig}}(\ell_\infty)$, for $\ell_\infty =$ `lineInfty q`, holds precisely when $f$ is a quotient $x/y$ of Laurent series with coefficients in $A$ whose denominator has nonzero coefficientwise reduction; `hIg`, which says that every $\ell$ is obtained as $\overline{\gamma}\cdot\ell_\infty$ for some $\gamma \in \Gamma_0(M')$ with $O_{\mathrm{Ig}}(\ell)$ the pullback of $O_{\mathrm{Ig}}(\ell_\infty)$ along `levelAutBar q M' ζ γ`; `hIg_inj`, injectivity of $\ell \mapsto O_{\mathrm{Ig}}(\ell)$; and `hIg_perm`, which says that for each index $\zeta'$ and each $\gamma \in \Gamma_0(M')$ pullback along `levelAutBar q M' ζ' γ` permutes the family $O_{\mathrm{Ig}}$.
--
--   The supersingular clauses are: `hSS_A`, that a constant $x \in \overline{\mathbb Q}$ lies in $O_{\mathrm{SS}}(s)$ if and only if $x \in A$; `hSS_over`, that for $s \in W$ and $f \in R_0.\mathrm{integers}$ which has non-negative order at every place of $\overline{F}(M')$ at which $\hat\jmath$ (the element of $\overline{F}(M')$ with Laurent expansion `coeffEmb jq`) has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\overline{F}_{q,M'}$ lies in $O_{\mathrm{SS}}(s)$, and moreover for every $a \in A$ whose residue equals the value at $s$ of the $R_0$-residue of $f$, the difference of the image of $f$ and the constant $a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$; `hSS_fix`, that each $O_{\mathrm{SS}}(s)$ is invariant under pullback along `levelAutBar q M' ζ' γ` for $\gamma \in \Gamma_0(M')$; and `hSS_tr`, that each $O_{\mathrm{SS}}(s)$ contains an element $t$ such that $t - a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a \in A$.
--
--   The descent data are: a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}$ algebraic over $K_0$ and $\pi \in K_0$; a henselian discrete valuation domain $A_0$ with an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ (`hιK₀`), such that the composite of $\iota$ with the residue map of $A$ is surjective (`hres`); a generator $\varpi_0$ of the maximal ideal of $A_0$ (`hϖ₀`) with $\iota(\varpi_0) = \pi$ (`hϖ₀π`); a subfield $F_0$ of $\overline{F}_{q,M'}$ characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that the image $\hat\jmath$ of `coeffEmb jq` lies in $F_0$, an $A_0$-algebra structure on $F_0$ with `hj₀` saying that its structure map is $a \mapsto \iota(a)$ viewed in $\overline{F}_{q,M'}$, and the requirement $\hat\jmath \neq 0$.
--
--   The chart data are: a valuation subring $V$ of $F_0$ with `hV` that $V$ maps into $O_{\mathrm{Ig}}(\ell_\infty)$, `hVlt` that this containment is strict, i.e. some element of $F_0$ lies in $O_{\mathrm{Ig}}(\ell_\infty)$ but not in $V$, and `hCV` that the finite chart ring $C =$ `chartAlgFin A₀ F₀ ĵ`, the set of elements of $F_0$ integral over $A_0[\hat\jmath]$, is contained in $V$; a maximal ideal $\mathfrak n$ of $C$ which by `h𝔫` consists exactly of those chart elements which are non-units of $V$, so that $\mathfrak n$ is the centre of $V$ on $C$; `hnotSS`, that $\mathfrak n$ is not a supersingular centre, in the sense that for every $s \in W$ some element of $C$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$ but not in $\mathfrak n$; a family $\mathfrak q$ of ideals of $C$ indexed by $\mathbb P^1(\mathbb Z/q)$ subject to `hLOC`, that for each $\ell$ an element $x \in F_0$ lies in $O_{\mathrm{Ig}}(\ell)$ exactly when $x = b/c$ with $b, c \in C$ and $c \notin \mathfrak q(\ell)$, `hMIN`, that each $\mathfrak q(\ell)$ is a minimal prime over the ideal of $C$ generated by the image of the maximal ideal of $A_0$, `hINJ`, injectivity of $\mathfrak q$, and `hSURJ`, that every minimal prime over that ideal is of the form $\mathfrak q(\ell)$; `hGENFIB`, that for every nonzero prime $\mathfrak p$ of $C$ not containing the image of $\varpi_0$ there is a valuation subring $V_1$ of $F_0$ consisting exactly of the quotients $b/c$ with $b, c \in C$ and $c \notin \mathfrak p$. Finally, $U$ is an open subscheme of the two-chart integral model `TwoChartIntegralModel A₀ F₀ ĵ` (the pushout glueing the spectra of the finite and infinite chart algebras) such that the image of the point $\mathfrak n$ under the canonical morphism `ιFin` from the spectrum of $C$ lies in $U$ (`hxU`), and such that the open immersion $U.\iota$ followed by the structure morphism `toBase` to $\mathrm{Spec}\, A_0$ is smooth (`hU`).
--
--   Under these hypotheses there exist an $A_0$-subalgebra $B$ of $F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that: (i) $B$ is finitely generated; (ii) $B$ is integrally closed in $F_0$, i.e. every $x \in F_0$ integral over $B$ lies in $B$; (iii) every $x \in F_0$ is of the form $b/c$ with $b, c \in B$ and $c \neq 0$; (iv) every prime $\mathfrak q$ of $B$ which contains the ideal generated by the image of the maximal ideal of $A_0$ and is not maximal is a minimal prime over that ideal; (v) for every nonzero prime $\mathfrak p$ of $B$ not containing that ideal there is a valuation subring $V_1$ of $F_0$ consisting exactly of the quotients $b/c$ with $b, c \in B$, $c \notin \mathfrak p$; (vi) if $\ell'$ is such that the image of all of $B$ lies in $O_{\mathrm{Ig}}(\ell')$, then $\ell' = \ell_\infty$; (vii) for no $s \in W$ is the image of all of $B$ contained in $O_{\mathrm{SS}}(s)$; (viii) there is a prime $\mathfrak q$ of $B$ such that $x \in F_0$ has image in $O_{\mathrm{Ig}}(\ell_\infty)$ exactly when $x = b/c$ with $b, c \in B$, $c \notin \mathfrak q$; (ix) the same localisation description of $O_{\mathrm{Ig}}(\ell_\infty)$ holds for every minimal prime $\mathfrak q$ of $B$ over the ideal generated by the image of the maximal ideal of $A_0$; (x) $B \subseteq V$; (xi) $\mathfrak m$ is the centre of $V$ on $B$, i.e. $b \in \mathfrak m$ if and only if $b$ is a non-unit of $V$; (xii) $\hat\jmath \in B$ or $\hat\jmath^{-1} \in B$; and (xiii) the structure map from $A_0$ to the localisation of $B$ at $\mathfrak m$ is formally smooth.
--
--   This is the packaging step on the good branch of the Igusa-chart dichotomy for the descended two-chart model of the full-level modular curve: starting from the finite chart ring $C$ with a centre $\mathfrak n$ that is neither an Igusa component centre other than $\ell_\infty$ nor a supersingular centre, and from smoothness of the model over $\mathrm{Spec}\,A_0$ near that centre, it produces a finitely generated, integrally closed $A_0$-subalgebra of $F_0$ with a single special-fibre component, centred at $V$, and with formally smooth local ring. It is used by [`ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent`](thm.html#ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent), the dichotomy statement for refinements of the Igusa Gauss ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent
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
    [Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0)]
    (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V)
    (hCV : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫max : 𝔫.IsMaximal)
    (h𝔫 : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits)

    (hnotSS : ∀ s : ↥W, ∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) ∧ g ∉ 𝔫)

    (𝔮 : CuspidalType.ProjLine q → Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))
    (hLOC : ∀ ℓ (x : ↥F₀), (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔
      ∃ b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∉ 𝔮 ℓ ∧ x * (c : ↥F₀) = (b : ↥F₀))
    (hMIN : ∀ ℓ, 𝔮 ℓ ∈ (Ideal.map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (maximalIdeal A₀)).minimalPrimes)
    (hINJ : Function.Injective 𝔮)
    (hSURJ : ∀ 𝔮' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      𝔮' ∈ (Ideal.map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (maximalIdeal A₀)).minimalPrimes → ∃ ℓ, 𝔮' = 𝔮 ℓ)

    (hGENFIB : ∀ 𝔭 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), 𝔭.IsPrime → 𝔭 ≠ ⊥ → algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∉ 𝔭 →
      ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀))

    (U : (AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).Opens)
    (hxU : (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫max.isPrime⟩ ∈ U)
    (hU : Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) :
    (∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal),

      B.FG ∧
      (∀ x : ↥F₀, _root_.IsIntegral ↥B x → x ∈ B) ∧
      (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
        𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
      (∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
        ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ ℓ' : CuspidalType.ProjLine q, (∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OIg ℓ') → ℓ' = lineInfty q) ∧
      (∀ s : ↥W, ¬ ∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s) ∧
      (∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔
        ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
        ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ b : ↥B, (b : ↥F₀) ∈ V) ∧ (∀ b : ↥B, b ∈ 𝔪 ↔ (b : ↥F₀) ∈ V.nonunits) ∧

      ((⟨_, hjF₀⟩ : ↥F₀) ∈ B ∨ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ ∈ B) ∧

      (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) := by sorry
