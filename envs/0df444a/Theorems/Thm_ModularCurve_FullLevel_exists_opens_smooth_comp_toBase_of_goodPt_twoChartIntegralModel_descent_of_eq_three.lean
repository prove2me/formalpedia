-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_three
-- name    : ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/ed8e1452-da6a-52fe-8bd1-27310984f742
-- title:
--   Smooth neighbourhood of an ordinary Igusa-branch point, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$ and a level $M'$ with $q \nmid M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, and a finset $W$ of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ whose members are exactly the supersingular places, i.e. the rational affine geometric places $w$ with $w.\mathrm{evalAt}$ of the geometric $j$-generator in $\mathrm{ssJSet}\,q$ (those $j$ for which every elliptic curve with that invariant has no nonzero $q$-torsion point). Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in that residue function field, compatible (hypothesis `hR₀`) with coefficientwise reduction of Laurent series with coefficients in $A$. Further data: $\pi \in \overline{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$; an index $\zeta$ of a primitive $q$-th root of unity; families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb Z/q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to: $O_{\mathrm{Ig}}(\infty)$ consists of the $f$ whose Laurent series is a quotient $x/y$ of series with coefficients in $A$ with $y$ of nonzero reduction; every $\ell$ is $\mathrm{redQ}\,q\,\gamma \cdot \infty$ for some $\gamma \in \Gamma_0(M')$ with $O_{\mathrm{Ig}}(\ell)$ the corresponding comap of $O_{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}$; $O_{\mathrm{Ig}}$ injective and permuted by all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; each $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ exactly in $A$, is fixed by all these automorphisms, contains an element $t$ with $t - a$ a unit for every $a \in A$, and satisfies the compatibility `hSS_over` between $R_0$-integral elements regular wherever $j$ is, their residues at $s$, and membership in, respectively the maximal ideal of, $O_{\mathrm{SS}}(s)$. Descent data: a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$; a henselian discrete valuation domain $A_0$ with an injective local ring map $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ and which is surjective onto $\mathrm{ResidueField}\,A$ after reduction; a uniformiser $\varpi_0$ generating the maximal ideal of $A_0$ with $\iota(\varpi_0) = \pi$; the subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$, which contains the image $\hat\jmath$ of the $q$-expansion of $j$, together with an $A_0$-algebra structure on $F_0$ induced by $\iota$, and $\hat\jmath \neq 0$. Let $x$ be a point of $\mathrm{TwoChartIntegralModel}\,A_0\,F_0\,\hat\jmath$ (the pushout gluing $\operatorname{Spec}$ of the subalgebra of elements of $F_0$ integral over $A_0[\hat\jmath]$ and of the one for $\hat\jmath^{-1}$) such that: $x$ lies over the closed point of $\operatorname{Spec} A_0$; $x$ specialises only to itself; for every point $y$ of either chart mapping to $x$, every chart element whose image in $\mathrm{fieldBar}\,q\,M'$ is a non-unit of $O_{\mathrm{Ig}}(\infty)$ lies in the prime ideal of $y$; and for every point $y$ of the finite chart over $x$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring map $\varphi$ from the finite chart algebra to $\Omega$ with kernel the prime of $y$, the value $\varphi(\hat\jmath)$ does not lie in $\mathrm{ssJSet}\,q\,\Omega$. Then there is an open subscheme $U$ of the two-chart model containing $x$ whose inclusion followed by the structure morphism to $\operatorname{Spec} A_0$ is smooth.
--
--   This is the $q = 3$ instance of the statement that an ordinary closed special point of the descended two-chart integral model lying on the $\infty$-Igusa (Gauss) branch admits a neighbourhood smooth over the henselian base $A_0$; it transports the corresponding assertion over $A$ through the descent data $(K_0, A_0, F_0)$. It feeds the dichotomy statement [`ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_three) on the Igusa-tower leg of the semistable covering construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
