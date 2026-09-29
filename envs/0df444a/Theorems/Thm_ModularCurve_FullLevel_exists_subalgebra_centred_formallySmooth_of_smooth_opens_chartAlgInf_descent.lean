-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent
-- name    : ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/5c789cff-a7ab-592b-a6d5-9812407ba0b4
-- title:
--   Formally smooth centred subalgebra at a smooth pole-chart centre
-- statement:
--   Throughout, $q$ is a prime with $5 \le q$, $M'$ is a nonzero natural number with $q \nmid M'$, and $A$ is a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ lies in `A.nonunits`. Further, $W$ is a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$, and `hW` says that $W$ consists exactly of the supersingular places in the sense of `ssPlaces q M' (ResidueField A)`: those $w$ which are rational, are affine geometric places, and have $w.\mathrm{evalAt}$ of the geometric $j$-generator in the supersingular $j$-set. The hypothesis `hle` states the inclusion of intermediate fields `modularFunctionFieldBar M' ≤ fieldBar q M'` of the Laurent series field over $\overline{\mathbb Q}$. Next, $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'` — a valuation subring `R₀.integers`, a surjective reduction homomorphism `R₀.residue` onto the target with kernel the maximal ideal, a map on places preserving degrees, compatibility with $A$ and with its residue map, and the scaling and divisor-pushforward clauses of that structure — and `hR₀` requires that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}$ lies in `modularFunctionFieldBar M'`, this image lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over `ResidueField A`, is the coefficientwise reduction of $y$. Finally $\pi \in \overline{\mathbb Q}$ satisfies $\pi^{q^2-1} = q$ and $\pi \in A$, and $\zeta$ is an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$.
--
--   Two families of valuation subrings of `fieldBar q M'` are given: $\mathcal O_{\mathrm{Ig}} =$ `OIg` indexed by [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21), the projective line over $\mathbb Z/q$, and $\mathcal O_{\mathrm{ss}} =$ `OSS` indexed by $W$. The Igusa group of hypotheses consists of: `hIg_inf`, that $f$ lies in `OIg (lineInfty q)` (the index $[1:0]$) precisely when there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot y = x$ after pushing $x,y$ forward along the inclusion of $A$; `hIg`, that for each $\ell$ there is $\gamma \in \Gamma_0(M')$ with `redQ q γ • lineInfty q = ℓ` and `OIg ℓ` the preimage of `OIg (lineInfty q)` under `levelAutBar q M' ζ γ`; `hIg_inj`, that `OIg` is injective; and `hIg_perm`, that for every $\zeta'$ in `Idx q` and every $\gamma \in \Gamma_0(M')$ there is a permutation $\sigma$ of the projective line with $(\mathcal O_{\mathrm{Ig},\ell})$ pulled back along `levelAutBar q M' ζ' γ` equal to $\mathcal O_{\mathrm{Ig},\sigma\ell}$ for all $\ell$.
--
--   The supersingular group consists of: `hSS_A`, that for each $s \in W$ and $x \in \overline{\mathbb Q}$ the image of $x$ lies in $\mathcal O_{\mathrm{ss},s}$ iff $x \in A$; `hSS_over`, that for $s \in W$ and $f \in$ `R₀.integers` inside `modularFunctionFieldBar M'` such that $f$ has nonnegative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the element $\hat\jmath$ coming from `coeffEmb (AlgebraicClosure ℚ) jq` has nonnegative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, the image of $f$ in `fieldBar q M'` lies in $\mathcal O_{\mathrm{ss},s}$ and, for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that residue of $f$, the difference of the image of $f$ and the image of $a$ lies in $\mathcal O_{\mathrm{ss},s}$ and in its maximal ideal; `hSS_fix`, that each $\mathcal O_{\mathrm{ss},s}$ is its own preimage under `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$; and `hSS_tr`, that for each $s$ there is $t \in \mathcal O_{\mathrm{ss},s}$ such that for every $a \in A$ the difference of $t$ and the image of $a$ lies in $\mathcal O_{\mathrm{ss},s}$ and is a unit there.
--
--   The descent data are: a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}$ algebraic over $K_0$ and $\pi \in K_0$; a henselian local domain $A_0$ which is a discrete valuation ring, together with an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ (`hιK₀`) and such that the composite of $\iota$ with the residue map of $A$ is surjective (`hres`); a generator $\varpi_0$ of the maximal ideal of $A_0$ (`hϖ₀`) with $\iota(\varpi_0) = \pi$ in $\overline{\mathbb Q}$ (`hϖ₀π`). Moreover $F_0$ is a subfield of `fieldBar q M'` characterised by `hF₀`: $f \in F_0$ iff every Laurent coefficient of $f$ lies in $K_0$; by `hjF₀` the element $\hat\jmath$ obtained from `coeffEmb (AlgebraicClosure ℚ) jq` lies in $F_0$, and it is assumed nonzero; and the given $A_0$-algebra structure on $F_0$ satisfies `hj₀`: the structure map is $\iota$ followed by the inclusion of $\overline{\mathbb Q}$ into `fieldBar q M'`.
--
--   Write $C$ for [`AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ ĵ`](def/AlgebraicCurve_TwoChartIntegralModel.html#L144), the pole chart, that is the $A_0$-subalgebra of $F_0$ of elements integral over $A_0[\hat\jmath^{-1}]$. The chart data are: a valuation subring $V$ of $F_0$ all of whose elements map into `OIg (lineInfty q)` (`hV`), with some element of $F_0$ lying in `OIg (lineInfty q)` but outside $V$ (`hVlt`), and with $C \subseteq V$ (`hCV`); and a maximal ideal $\mathfrak n$ of $C$ which is the centre of $V$ on $C$, in the sense that $g \in \mathfrak n$ iff $g$ lies in `V.nonunits` (`h𝔫`). The hypothesis `hnotSS` states that for every $s \in W$, either some element of $C$ lies in the maximal ideal of $\mathcal O_{\mathrm{ss},s}$ but not in $\mathfrak n$, or some element of $C$ has image outside $\mathcal O_{\mathrm{ss},s}$.
--
--   The component data are a family $\mathfrak q$ of ideals of $C$ indexed by the projective line with: `hLOC`, for each $\ell$ and $x \in F_0$, the image of $x$ lies in $\mathcal O_{\mathrm{Ig},\ell}$ iff $x = b/c$ with $b, c \in C$ and $c \notin \mathfrak q_\ell$; `hMIN`, each $\mathfrak q_\ell$ is a minimal prime over the ideal of $C$ generated by the image of the maximal ideal of $A_0$; `hINJ`, injectivity of $\ell \mapsto \mathfrak q_\ell$; and `hSURJ`, every minimal prime over that ideal is one of the $\mathfrak q_\ell$. The hypothesis `hGENFIB` requires that every nonzero prime $\mathfrak p$ of $C$ not containing the image of $\varpi_0$ admits a valuation subring $V_1$ of $F_0$ whose elements are exactly the fractions $b/c$ with $b, c \in C$, $c \notin \mathfrak p$. Finally, $U$ is an open subscheme of the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ ĵ`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) (the pushout of the two chart spectra along the middle chart) which contains the image of the point $\mathfrak n$ under the morphism `ιInf` from the spectrum of $C$ (`hxU`), and the open immersion $U.\iota$ followed by the structure morphism `toBase` to $\operatorname{Spec} A_0$ is smooth (`hU`).
--
--   Under these hypotheses there exist an $A_0$-subalgebra $B$ of $F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that all of the following hold. First, $B$ is finitely generated (`B.FG`). Second, $B$ is integrally closed in $F_0$: every $x \in F_0$ integral over $B$ lies in $B$. Third, $F_0$ is the fraction field of $B$: every $x \in F_0$ is of the form $b/c$ with $b, c \in B$, $c \neq 0$. Fourth, every prime $\mathfrak q$ of $B$ which contains the image of the maximal ideal of $A_0$ and is not maximal is a minimal prime over that image ideal. Fifth, for every nonzero prime $\mathfrak p$ of $B$ not containing the image of the maximal ideal of $A_0$ there is a valuation subring $V_1$ of $F_0$ whose elements are exactly the fractions $b/c$ with $b, c \in B$ and $c \notin \mathfrak p$. Sixth, for every $\ell$ in the projective line, if every element of $B$ has image in $\mathcal O_{\mathrm{Ig},\ell}$ then $\ell =$ `lineInfty q`. Seventh, for every $s \in W$ it is not the case that every element of $B$ has image in $\mathcal O_{\mathrm{ss},s}$. Eighth, there is a prime ideal $\mathfrak q$ of $B$ such that for all $x \in F_0$ the image of $x$ lies in `OIg (lineInfty q)` iff $x = b/c$ with $b, c \in B$ and $c \notin \mathfrak q$. Ninth, every minimal prime $\mathfrak q$ over the image of the maximal ideal of $A_0$ in $B$ has this same property: the image of $x \in F_0$ lies in `OIg (lineInfty q)` iff $x = b/c$ with $b, c \in B$, $c \notin \mathfrak q$. Tenth, every element of $B$ lies in $V$, and an element of $B$ lies in $\mathfrak m$ iff it lies in `V.nonunits`. Eleventh, $\hat\jmath \in B$ or $\hat\jmath^{-1} \in B$. Twelfth, the structure map from $A_0$ to the localisation `Localization.AtPrime 𝔪` is formally smooth.
--
--   This is the packaging step on the pole chart of the Igusa-chart dichotomy for the descended full-level field: at a centre $\mathfrak n$ of the refinement $V$ which is not a supersingular centre and at which the two-chart integral model is smooth over $\operatorname{Spec} A_0$, a suitable finitely generated, integrally closed subalgebra $B$ of $F_0$ carries all the ring-theoretic and valuation-theoretic clauses of the good branch, with formally smooth localisation at the centre $\mathfrak m$. It is used by [`ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent`](thm.html#ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent), the dichotomy itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent.lean

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

theorem ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent
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
    (hCV : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫max : 𝔫.IsMaximal)
    (h𝔫 : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits)

    (hnotSS : ∀ s : ↥W, (∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
        (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) ∧ g ∉ 𝔫) ∨
      (∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) ∉ OSS s))

    (𝔮 : CuspidalType.ProjLine q → Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))
    (hLOC : ∀ ℓ (x : ↥F₀), (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔
      ∃ b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∉ 𝔮 ℓ ∧ x * (c : ↥F₀) = (b : ↥F₀))
    (hMIN : ∀ ℓ, 𝔮 ℓ ∈ (Ideal.map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (maximalIdeal A₀)).minimalPrimes)
    (hINJ : Function.Injective 𝔮)
    (hSURJ : ∀ 𝔮' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      𝔮' ∈ (Ideal.map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (maximalIdeal A₀)).minimalPrimes → ∃ ℓ, 𝔮' = 𝔮 ℓ)

    (hGENFIB : ∀ 𝔭 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), 𝔭.IsPrime → 𝔭 ≠ ⊥ → algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∉ 𝔭 →
      ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀))

    (U : (AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).Opens)
    (hxU : (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫max.isPrime⟩ ∈ U)
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
