-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_two
-- name    : ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/866c30b8-0a7b-5e0a-89cb-99063c72f36b
-- title:
--   Smooth neighbourhood of a good ordinary point, descended model, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\operatorname{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places (rational, affine geometric, and with $\mathrm{evalAt}$ of the geometric $j$-generator a supersingular value). Assume $\operatorname{modularFunctionFieldBar} M' \le \operatorname{fieldBar} q M'$, and let $R_0$ be a constant reduction of $\operatorname{modularFunctionFieldBar} M'$ along $A$ with values in $\operatorname{modularFunctionFieldC}(\mathrm{ResidueField}\,A,M')$, compatible (hypothesis $hR_0$) with coefficientwise reduction of Laurent series with coefficients in $A$. Let $\pi \in \overline{\mathbb Q}$ satisfy $\pi^{q^2-1}=q$ and $\pi \in A$, let $\zeta$ index a primitive $q$-th root of unity, and let $\ell \mapsto \mathcal O_{\mathrm{Ig},\ell}$ ($\ell \in \mathbb P^1(\mathbb F_q)$) and $s \mapsto \mathcal O_{\mathrm{ss},s}$ ($s \in W$) be families of valuation subrings of $\operatorname{fieldBar} q M'$ subject to: $\mathcal O_{\mathrm{Ig},\infty}$ consists of the $f$ whose Laurent expansion is a quotient $x/y$ of series with coefficients in $A$ with $y$ of nonzero reduction; each $\mathcal O_{\mathrm{Ig},\ell}$ is the pullback of $\mathcal O_{\mathrm{Ig},\infty}$ along $\operatorname{levelAutBar} q M' \zeta \gamma$ for some $\gamma \in \Gamma_0(M')$ carrying $\infty$ to $\ell$; the family is injective and is permuted by all $\operatorname{levelAutBar} q M' \zeta' \gamma$ with $\gamma \in \Gamma_0(M')$; each $\mathcal O_{\mathrm{ss},s}$ meets $\overline{\mathbb Q}$ exactly in $A$, is fixed by all those automorphisms, contains an element $t$ with $t-a$ a unit for every $a \in A$, and receives the $R_0$-integers $f$ that are regular wherever $\hat\jmath$ is, with $f-a$ in the maximal ideal whenever $\bar a = \mathrm{evalAt}_s(\bar f)$. Let $K_0$ be a subfield of $\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$, let $A_0$ be a henselian discrete valuation domain with an injective local ring homomorphism $\iota : A_0 \to A$ whose image is $A \cap K_0$ and which induces a surjection onto the residue field of $A$, and let $\varpi_0$ generate the maximal ideal of $A_0$ with $\iota(\varpi_0) = \pi$. Let $F_0$ be the subfield of $\operatorname{fieldBar} q M'$ of elements all of whose Laurent coefficients lie in $K_0$, an $A_0$-algebra via $\iota$, and assume the image $\hat\jmath$ of the $j$-expansion lies in $F_0$ and is nonzero. Let $x$ be a point of the two-chart integral model $\mathfrak X = \operatorname{TwoChartIntegralModel}(A_0, F_0, \hat\jmath)$, the pushout of the two affine charts $\operatorname{Spec}$ of the elements of $F_0$ integral over $A_0[\hat\jmath]$ and over $A_0[\hat\jmath^{-1}]$, such that: $x$ maps to the closed point of $\operatorname{Spec} A_0$; $x$ specialises only to itself; for every point $y$ of either chart lying over $x$, every chart element whose image in $\operatorname{fieldBar} q M'$ is a non-unit of $\mathcal O_{\mathrm{Ig},\infty}$ lies in the prime of $y$; and for every point $y$ of the $\hat\jmath$-finite chart over $x$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from that chart to $\Omega$ with kernel the prime of $y$, the value $\varphi(\hat\jmath)$ is not a supersingular $j$-value in $\Omega$ (i.e. some elliptic curve over $\Omega$ with that invariant has a nonzero $q$-torsion point). Then there is an open subscheme $U$ of $\mathfrak X$ containing $x$ such that the inclusion of $U$ followed by $\mathfrak X \to \operatorname{Spec} A_0$ is smooth.
--
--   This is the smoothness statement for a closed special point of the descended two-chart integral model which lies on the $\infty$ (Igusa–Gauss) branch and is ordinary, in the case $q=2$; it is the counterpart of the same statement for $q \ge 5$. It feeds the dichotomy step which, at a closed special point of the descended model, either produces a centred formally smooth chart subalgebra or exhibits a family of functions lying in the non-units of the relevant Gauss ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))

    (hx₀ : (AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base x = closedPoint A₀)
    (hxcl : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), x ⤳ y → y = x)

    (hxFin : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          ((b : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → b ∈ y.asIdeal)
    (hxInf : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          ((b : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → b ∈ y.asIdeal)

    (hord : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ∉ ModularCurve.ssJSet q Ω) :
    ∃ U : (AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).Opens, x ∈ U ∧ Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := by sorry
