-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_chartAlgInf_descent
-- name    : ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_chartAlgInf_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/39bddee2-89a5-546a-86b5-372031adebc9
-- title:
--   Cusp centre on the ∞-chart is a closed special point
-- statement:
--   Fix a prime $q\ge 5$ and a level $M'$ with $M'\neq 0$ and $q\nmid M'$; let $A\subseteq\overline{\mathbb Q}$ be a valuation subring with $q$ a non-unit of $A$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\kappa(A),M')$ over $\kappa(A)=\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places (rational, affine geometric, with $\mathrm{evalAt}$ of the geometric $j$ in the supersingular set), let $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}(\kappa(A),M')$ (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map with kernel the maximal ideal, compatible with $A$ and with place maps) satisfying $hR_0$: coefficientwise reduction of any Laurent series over $A$ lying in $\mathrm{modularFunctionFieldBar}\,M'$ agrees with $R_0.\mathrm{residue}$. Let $\pi\in A$ with $\pi^{q^2-1}=q$, let $\zeta$ be an index for primitive $q$-th roots of unity, and let $O_{\mathrm{Ig}}$ assign a valuation subring of $\mathrm{fieldBar}\,q\,M'$ to each point of $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}$ one to each $s\in W$, subject to: $O_{\mathrm{Ig}}(\infty)$ consists of the quotients $x/y$ of Laurent series with coefficients in $A$ with $y$ of nonzero reduction; each $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\infty)$ along a level automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma\in\Gamma_0(M')$ carrying $\infty$ to $\ell$; $O_{\mathrm{Ig}}$ is injective; the level automorphisms permute the family $O_{\mathrm{Ig}}$; each $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ in exactly $A$, is fixed by all level automorphisms, and contains an element $t$ such that $t-a$ is a unit for every $a\in A$; and, for $f\in R_0.\mathrm{integers}$ of nonnegative order at every place at which the image of $j_q$ has nonnegative order, if $R_0.\mathrm{residue}\,f$ lies in the valuation ring of $s$ then the image of $f$ lies in $O_{\mathrm{SS}}(s)$, and $f-a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$ whenever $a\in A$ reduces to the value of $R_0.\mathrm{residue}\,f$ at $s$. Let $K_0\subseteq\overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$, let $A_0$ be a henselian discrete valuation ring with an injective local ring map $\iota:A_0\to A$ whose image is $A\cap K_0$ and which induces a surjection onto $\kappa(A)$, and let $\varpi_0$ generate the maximal ideal of $A_0$ with $\iota\varpi_0=\pi$. Let $F_0\subseteq \mathrm{fieldBar}\,q\,M'$ be the subfield of elements all of whose Laurent coefficients lie in $K_0$, an $A_0$-algebra via $\iota$, and let $\hat\jmath\in F_0$ be the image of the $q$-expansion of $j$, assumed nonzero. Finally let $V$ be a valuation subring of $F_0$ contained in $O_{\mathrm{Ig}}(\infty)$ but not equal to $O_{\mathrm{Ig}}(\infty)\cap F_0$ (some element of $F_0$ lies in $O_{\mathrm{Ig}}(\infty)$ yet not in $V$), with $\hat\jmath\notin V$, containing the chart algebra $\mathrm{chartAlgInf}\,A_0\,F_0\,\hat\jmath$ of elements of $F_0$ integral over $A_0[\hat\jmath^{-1}]$, and let $\mathfrak n$ be a prime ideal of that chart algebra consisting exactly of the elements that are non-units of $V$. Writing $x$ for the image of $\mathfrak n$ in $\mathrm{TwoChartIntegralModel}\,A_0\,F_0\,\hat\jmath$ under $\mathrm{ i\iota Inf}$, the conclusion is fourfold: $\mathrm{toBase}$ sends $x$ to the closed point of $\operatorname{Spec}A_0$; every point $y$ with $x\rightsquigarrow y$ equals $x$, so $x$ is closed; no point of the finite chart $\mathrm{XFin}$ is sent to $x$ by $\mathrm{ i\iota Fin}$; and for every point $y$ of $\mathrm{XInf}$ with $\mathrm{ i\iota Inf}(y)=x$, every element of the chart algebra whose image in $\mathrm{fieldBar}\,q\,M'$ is a non-unit of $O_{\mathrm{Ig}}(\infty)$ belongs to the prime ideal of $y$.
--
--   This is the cusp-branch bookkeeping step for the descended two-chart integral model of the full-level modular curve: a proper valuation-theoretic refinement $V$ of the Igusa ring at $\infty$ which does not contain $\hat\jmath$ has its centre on the pole chart at a point of the glued model which is closed, lies over the closed point of $\operatorname{Spec}A_0$, is not met by the finite chart, and absorbs all chart functions that are non-units at the Igusa place. It feeds the step producing a centred subalgebra with a formally smooth neighbourhood, or else a prime consisting of non-units, for the descended Gauss ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_chartAlgInf_descent.lean

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

theorem ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_chartAlgInf_descent
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
    (hjV : (⟨_, hjF₀⟩ : ↥F₀) ∉ V)
    (hCV : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫p : 𝔫.IsPrime)
    (h𝔫 : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits) :
    (AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ((AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) = closedPoint A₀ ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ ⤳ y →
      y = (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y ≠ (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          ((b : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → b ∈ y.asIdeal) := by sorry
