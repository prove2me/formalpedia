-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_three
-- name    : ModularCurve.FullLevel.isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/9c3aee4c-70ad-58ad-9810-957e14be1533
-- title:
--   Maximality of the centre of V on an Igusa chart algebra (q=3)
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'\ge 1$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. The data are: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}(\kappa_A,M')$ over the residue field $\kappa_A$ of $A$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular set); the inclusion $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ of subfields of $\overline{\mathbb Q}$-Laurent series; a constant reduction $R_0$ of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$, compatible coefficientwise with reduction of Laurent series over $A$; an element $\pi\in A$ with $\pi^{q^2-1}=q$; an index $\zeta$ of a primitive $q$-th root of unity; families $O_{\mathrm{Ig}}$ over $\mathbb P^1(\mathbb Z/q)$ and $O_{\mathrm{SS}}$ over $W$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$, subject to the Igusa conditions (description of $O_{\mathrm{Ig}}(\infty)$ by quotients of Laurent series over $A$, $\Gamma_0(M')$-transitivity through the automorphisms $\mathrm{levelAutBar}$, injectivity, and permutation of the family by these automorphisms) and the supersingular conditions (contraction to $A$ on $\overline{\mathbb Q}$, compatibility of $R_0$-reduction with the place attached to $s$ together with a congruence for elements of $A$, $\Gamma_0(M')$-invariance, and existence of a trace element $t$ whose translates by elements of $A$ are units); descent data consisting of a subfield $K_0\subseteq\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$, a henselian discrete valuation ring $A_0$ with an injective local homomorphism $\iota:A_0\to A$ whose image is $A\cap K_0$, surjective on residue fields, and a uniformiser $\varpi_0$ of $A_0$ with $\iota(\varpi_0)=\pi$; the subfield $F_0\subseteq \mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of $j$ and carrying an $A_0$-algebra structure induced by $\iota$, with $\hat\jmath\ne 0$; and $S$ equal to $\{\hat\jmath\}$ or $\{\hat\jmath^{-1}\}$. Finally let $V$ be a valuation subring of $F_0$ contained in the contraction of $O_{\mathrm{Ig}}(\infty)$ to $F_0$ and properly so, in the sense that some $f\in F_0$ lies in $O_{\mathrm{Ig}}(\infty)$ but not in $V$, assume the chart algebra $\mathrm{chartAlg}\,A_0\,F_0\,S$ (the elements of $F_0$ integral over $A_0[S]$) is contained in $V$, and let $\mathfrak n$ be an ideal of that chart algebra consisting exactly of those of its elements that are non-units of $V$. Then $\mathfrak n$ is a maximal ideal.
--
--   This is the statement that the centre on a chart algebra of the two-chart integral model, cut out by a valuation subring refining the Igusa valuation at $\infty$, is a maximal ideal, in the case $q=3$ of the construction of semistable coverings of modular curves. It is invoked in the identification of such centres with closed points of the model and in the associated formal-smoothness dichotomy.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_three
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
    (S : Set ↥F₀) (hS : S = {(⟨_, hjF₀⟩ : ↥F₀)} ∨ S = {(⟨_, hjF₀⟩ : ↥F₀)⁻¹})
    (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V)
    (hCV : ∀ g : ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S)) (h𝔫 : ∀ g : ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits) :
    𝔫.IsMaximal := by sorry
