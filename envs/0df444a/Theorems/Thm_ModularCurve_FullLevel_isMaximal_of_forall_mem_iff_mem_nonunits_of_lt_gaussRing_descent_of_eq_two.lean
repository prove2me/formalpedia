-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two
-- name    : ModularCurve.FullLevel.isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/2cd6df30-d22c-5c06-8872-3e9b9cbc86ff
-- title:
--   Maximality of the centre of V on a chart algebra, q=2
-- statement:
--   Fix a prime $q$ with $q=2$, a nonzero level $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ in which $q$ is a non-unit. Let $W$ be the finite set of places $w$ of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ that are rational, affine geometric and send the geometric $j$-invariant into the supersingular set, assume the base-changed full level-$M'$ field $\mathrm{modularFunctionFieldBar}\,M'$ is contained in $F=\mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in that level-$M'$ function field over the residue field, compatible with coefficientwise reduction of Laurent series over $A$. Fix $\pi\in A$ with $\pi^{q^2-1}=q$, a primitive $q$-th root of unity $\zeta$, and families $O_{\mathrm{Ig}}$ of valuation subrings of $F$ indexed by $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to: the Gauss-ring description of $O_{\mathrm{Ig}}(\infty)$ by quotients of Laurent series over $A$, transitivity of $\Gamma_0(M')$ on the index set via $\mathrm{levelAutBar}$, injectivity of $O_{\mathrm{Ig}}$ and permutation of its members under $\mathrm{levelAutBar}$; and for each $s\in W$: $O_{\mathrm{SS}}(s)\cap\overline{\mathbb Q}=A$, compatibility of $O_{\mathrm{SS}}(s)$ and its maximal ideal with $R_0$-residues at $s$ for elements regular wherever $\hat\jmath$ is, $\mathrm{levelAutBar}$-invariance, and existence of $t\in O_{\mathrm{SS}}(s)$ with $t-a$ a unit for all $a\in A$. Fix a subfield $K_0\subseteq\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$, a henselian discrete valuation domain $A_0$ with an injective local homomorphism $\iota:A_0\to A$ whose image is $A\cap K_0$, inducing a surjection on residue fields, and a uniformiser $\varpi_0$ with $\iota(\varpi_0)=\pi$. Let $F_0\subseteq F$ be the subfield of elements all of whose Laurent coefficients lie in $K_0$; it contains the image $\hat\jmath$ of $j$, assumed nonzero, and carries an $A_0$-algebra structure extending $\iota$. Let $S=\{\hat\jmath\}$ or $S=\{\hat\jmath^{-1}\}$, and let $V$ be a valuation subring of $F_0$ whose elements all land in $O_{\mathrm{Ig}}(\infty)$, with some element of $F_0$ landing in $O_{\mathrm{Ig}}(\infty)$ yet outside $V$, such that the chart algebra $\mathrm{chartAlg}\,A_0\,F_0\,S$ of elements integral over $A_0[S]$ is contained in $V$. Then any ideal $\mathfrak n$ of that chart algebra consisting exactly of its elements that are non-units of $V$ is maximal.
--
--   This identifies the centre of the valuation ring $V$ on a chart algebra of the two-chart integral model of $F_0$ over $A_0$ as a maximal ideal, in the Igusa-chart setting at $q=2$; it is the $q=2$ counterpart of the corresponding statement for larger $q$. It is used in locating closed points of the two-chart model and in the construction of the semistable covering data for the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two.lean

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

theorem ModularCurve.FullLevel.isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two
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
    (S : Set ↥F₀) (hS : S = {(⟨_, hjF₀⟩ : ↥F₀)} ∨ S = {(⟨_, hjF₀⟩ : ↥F₀)⁻¹})
    (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V)
    (hCV : ∀ g : ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S)) (h𝔫 : ∀ g : ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits) :
    𝔫.IsMaximal := by sorry
