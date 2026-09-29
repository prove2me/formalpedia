-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two
-- name    : ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/0843abe4-07cc-5b0a-bdeb-aa6537a7702d
-- title:
--   Descended Igusa centre is a closed special point (q=2)
-- statement:
--   Fix the prime $q$ together with the hypothesis $q=2$, a level $M'\neq 0$ with $q\nmid M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, and a finite set $W$ of places of $\mathrm{modularFunctionFieldC}$ over the residue field of $A$ consisting exactly of the supersingular places (rational, affine geometric, with $j$-value in the supersingular set). Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map onto $\mathrm{modularFunctionFieldC}$ over $\mathrm{ResidueField}\,A$ with kernel the maximal ideal, contracting to $A$ and compatible with residues of constants, together with a degree- and order-preserving map on places), subject to $hR_0$: coefficientwise reduction of Laurent series with coefficients in $A$ agrees with $R_0$'s residue. Further data: $\pi\in A$ with $\pi^{q^2-1}=q$; an index $\zeta$ of a primitive $q$-th root of unity; families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}$ indexed by $W$. The hypotheses on these families are: $O_{\mathrm{Ig}}(\infty)$ consists of the quotients $x/y$ of Laurent series with coefficients in $A$ whose denominator has non-zero coefficientwise reduction; $\Gamma_0(M')$ acts transitively on the $O_{\mathrm{Ig}}(\ell)$ through $\mathrm{levelAutBar}$ and permutes them, and $\ell\mapsto O_{\mathrm{Ig}}(\ell)$ is injective; each $O_{\mathrm{SS}}(s)$ contracts to $A$ on constants, is $\Gamma_0(M')$-invariant under all $\mathrm{levelAutBar}$, reduces $j$-regular elements of $R_0.\mathrm{integers}$ compatibly with the place $s$ (membership plus congruence of residues modulo the maximal ideal), and contains an element whose differences with all constants from $A$ are units. On the descent side: a subfield $K_0\subseteq\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$; a henselian discrete valuation domain $A_0$ with an injective local ring map $\iota:A_0\to A$ whose image is $A\cap K_0$, surjective on residue fields, and a uniformiser $\varpi_0$ of $A_0$ with $\iota(\varpi_0)=\pi$; the subfield $F_0\subseteq \mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$, an $A_0$-algebra structure on $F_0$ induced by $\iota$, and the element $\hat\jmath\in F_0$ given by the $q$-expansion of $j$, assumed non-zero. Finally, let $V$ be a valuation subring of $F_0$ contained in $O_{\mathrm{Ig}}(\infty)$, properly so in the sense that some element of $F_0$ lying in $O_{\mathrm{Ig}}(\infty)$ is not in $V$, containing the finite chart algebra $C=\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$, and let $\mathfrak n\subseteq C$ be a prime ideal equal to the centre of $V$, i.e. $g\in\mathfrak n$ iff $g$ is a non-unit of $V$. Write $x$ for the image of $\mathfrak n$ in the two-chart integral model $\mathfrak X=\mathrm{TwoChartIntegralModel}\,A_0\,F_0\,\hat\jmath$ (the pushout of the two chart spectra) under the finite-chart morphism $\iota_{\mathrm{Fin}}$. The conclusion has four parts: the structure morphism $\mathrm{toBase}$ sends $x$ to the closed point of $\operatorname{Spec} A_0$; every point to which $x$ specialises equals $x$, so $x$ is closed in $\mathfrak X$; and for every point $y$ of the finite chart $\mathrm{XFin}$ (respectively of the pole chart $\mathrm{XInf}$) mapping to $x$, every element of $\mathrm{chartAlgFin}$ (respectively $\mathrm{chartAlgInf}$) whose image in $\mathrm{fieldBar}\,q\,M'$ is a non-unit of $O_{\mathrm{Ig}}(\infty)$ belongs to the prime ideal of $y$.
--
--   This is the $q=2$ case of the statement that a proper refinement of the Igusa Gauss ring at $\infty$, descended to the coefficient field $K_0$ and the henselian base $A_0$, has as centre a closed point of the two-chart integral model lying over the closed point of $\operatorname{Spec} A_0$, with the non-units of the Gauss ring vanishing at every chart point above it. It feeds the dichotomy used to produce a centred formally smooth subalgebra or a uniform non-unit locus on the descended model along the Igusa branch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two.lean

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

theorem ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two
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
    (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V)
    (hCV : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫p : 𝔫.IsPrime)
    (h𝔫 : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits) :
    (AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) = closedPoint A₀ ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ ⤳ y →
      y = (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          ((b : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → b ∈ y.asIdeal) ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          ((b : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → b ∈ y.asIdeal) := by sorry
