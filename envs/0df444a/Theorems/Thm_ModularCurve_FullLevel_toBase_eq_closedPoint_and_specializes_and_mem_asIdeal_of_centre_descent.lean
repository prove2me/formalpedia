-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent
-- name    : ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/f1503b88-2eec-5da2-b3ef-d8bb0799b2da
-- title:
--   Centre of a refined Gauss ring is a closed special point
-- statement:
--   Let $q\ge 5$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and $A$ a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a nonunit; let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular set), let $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ via `hle`, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$, whose residue is computed coefficientwise on Laurent series with coefficients in $A$ (`hR₀`). Fix $\pi\in A$ with $\pi^{q^2-1}=q$, an index $\zeta$ of a primitive $q$th root of unity, and families $O_{\mathrm{Ig}}$ on $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}$ on $W$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$: $O_{\mathrm{Ig}}(\infty)$ is the Gauss ring of quotients $x/y$ of Laurent series over $A$ with $y$ of nonzero reduction, the remaining $O_{\mathrm{Ig}}(\ell)$ arise from it by $\Gamma_0(M')$-translation under $\mathrm{levelAutBar}$, $O_{\mathrm{Ig}}$ is injective and $\Gamma_0(M')$ permutes its values; the $O_{\mathrm{SS}}(s)$ contract to $A$ on constants, are compatible with $R_0$ and its residues at $s$, are $\Gamma_0(M')$-invariant, and admit an element $t$ with all differences $t-a$ ($a\in A$) units (these hypotheses on $O_{\mathrm{Ig}}$ and $O_{\mathrm{SS}}$ are summarised here). Let $K_0\subseteq\overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$, and let $A_0$ be a henselian discrete valuation domain with an injective local homomorphism $\iota:A_0\to A$ whose image is $A\cap K_0$, with $\mathrm{residue}\circ\iota$ surjective, with $\mathfrak m_{A_0}=(\varpi_0)$ and $\iota\varpi_0=\pi$. Let $F_0$ be the subfield of $\mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$, an $A_0$-algebra via $\iota$, containing the element $\hat\jmath$ coming from the $q$-expansion $\mathrm{jq}$ of $j$, which is assumed nonzero. Finally let $V$ be a valuation subring of $F_0$ contained in $O_{\mathrm{Ig}}(\infty)$, strictly so in the sense that some element of $F_0\cap O_{\mathrm{Ig}}(\infty)$ is not in $V$, containing the finite chart algebra $C=\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$ of elements integral over $A_0[\hat\jmath]$, and let $\mathfrak n$ be a prime ideal of $C$ consisting exactly of the elements lying in the nonunits of $V$. Then, writing $x$ for the image of $\mathfrak n$ in the two-chart integral model $\mathfrak X=\mathrm{TwoChartIntegralModel}\,A_0\,F_0\,\hat\jmath$ under the finite-chart morphism $\iota_{\mathrm{Fin}}$: the structure morphism $\mathrm{toBase}$ sends $x$ to the closed point of $\operatorname{Spec} A_0$; every $y\in\mathfrak X$ with $x\rightsquigarrow y$ equals $x$; and for every point $y$ of $\operatorname{Spec} C$ with $\iota_{\mathrm{Fin}}(y)=x$, every $b\in C$ whose image in $\mathrm{fieldBar}\,q\,M'$ is a nonunit of $O_{\mathrm{Ig}}(\infty)$ lies in $y$, and likewise for every point $y$ of $\operatorname{Spec}(\mathrm{chartAlgInf}\,A_0\,F_0\,\hat\jmath)$ with $\iota_{\mathrm{Inf}}(y)=x$.
--
--   This is the two-chart bookkeeping step for the descended Igusa model: the centre $\mathfrak n$ of a proper valuation-ring refinement $V$ of the Gauss ring on the $K_0$-rational subfield $F_0$ is a closed point of the glued model lying in the special fibre over $A_0$, and in either chart the functions that are nonunits of the Gauss ring vanish at every point above it. It is used by [`ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent`](thm.html#ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent) to pass from such a point to a formally smooth neighbourhood or to the alternative containment of nonunits.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent.lean

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

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open ModularCurve.FullLevel
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent
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
