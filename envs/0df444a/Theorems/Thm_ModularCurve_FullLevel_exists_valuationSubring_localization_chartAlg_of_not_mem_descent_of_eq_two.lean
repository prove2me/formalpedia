-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent_of_eq_two
-- name    : ModularCurve.FullLevel.exists_valuationSubring_localization_chartAlg_of_not_mem_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/d3a5821a-5208-5821-be47-9eede30642a0
-- title:
--   Chart-algebra localisations away from varpi₀ are valuation rings (q=2)
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a non-zero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit, with residue field $k_A$. Let $W$ be a finite set of places of the field `modularFunctionFieldC k_A M'` (generated over $k_A$ by the two Laurent series `jqModC` and `jqNModC`) consisting exactly of the supersingular places, i.e. of the rational affine geometric places whose $j$-value lies in the supersingular set. Assume the base-changed full modular function field `modularFunctionFieldBar M'` is contained in `fieldBar q M'`, and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` along $A$ with values in `modularFunctionFieldC k_A M'` (a valuation subring of integers, a surjective residue map with kernel its maximal ideal, compatible with $A$ and with orders of functions under a place map preserving degrees), subject to the compatibility that for a Laurent series $y$ over $A$ whose coefficientwise image lies in `modularFunctionFieldBar M'`, that image lies in the integers of $R_0$ and its $R_0$-residue is the coefficientwise reduction of $y$. Fix $\pi \in A$ with $\pi^{q^2-1} = q$ and a primitive $q$-th root of unity $\zeta$, and two families of valuation subrings of `fieldBar q M'`: an Igusa family $O_{\mathrm{Ig}}$ indexed by $\mathbb P^1(\mathbb Z/q)$ and a family $O_{\mathrm{SS}}$ indexed by $W$. The Igusa hypotheses are: membership in $O_{\mathrm{Ig}}(\infty)$ is the existence of Laurent series $x, y$ over $A$ with the reduction of $y$ non-zero and $f\,y = x$; every $\ell$ arises from some $\gamma \in \Gamma_0(M')$ with $\overline\gamma \cdot \infty = \ell$ and $O_{\mathrm{Ig}}(\ell)$ the pullback of $O_{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`; $O_{\mathrm{Ig}}$ is injective; and pullback along `levelAutBar q M' ζ' γ`, $\gamma \in \Gamma_0(M')$, permutes the family. The supersingular hypotheses are: $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ in exactly $A$; for $f$ in the integers of $R_0$ which is regular at every place where $j$ is regular and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ lies in $O_{\mathrm{SS}}(s)$ and $f - a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$ whenever $a \in A$ reduces to the value of the residue of $f$ at $s$; each $O_{\mathrm{SS}}(s)$ is invariant under all pullbacks `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; and each $O_{\mathrm{SS}}(s)$ contains an element $t$ with $t - a$ a unit for every $a \in A$. Let $K_0$ be a subfield of $\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$, and let $A_0$ be a henselian discrete valuation domain with an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$, inducing a surjection onto $k_A$, and with uniformiser $\varpi_0$ satisfying $\iota(\varpi_0) = \pi$. Let $F_0$ be the subfield of `fieldBar q M'` of those elements all of whose Laurent coefficients lie in $K_0$, assume the image $\hat\jmath$ of $j$ lies in $F_0$ and is non-zero, and let $F_0$ be an $A_0$-algebra whose structure map is induced by $\iota$. Finally let $S = \{\hat\jmath\}$ or $S = \{\hat\jmath^{-1}\}$, and let $\mathfrak p$ be a non-zero prime ideal of the chart algebra `TwoChartIntegralModel.chartAlg A₀ F₀ S` (the $A_0$-subalgebra of $F_0$ of elements integral over $A_0[S]$) not containing the image of $\varpi_0$. Then there is a valuation subring $V_1$ of $F_0$ whose elements are exactly the quotients $b/c$ with $b$, $c$ in the chart algebra and $c \notin \mathfrak p$; that is, the localisation of the chart algebra at $\mathfrak p$ is a valuation ring of $F_0$.
--
--   This is the generic-fibre statement that the descended two-chart integral model of the full-level modular curve is regular away from the uniformiser: at a non-zero prime of a chart algebra not containing $\varpi_0$ the localisation is a valuation ring of the descended function field $F_0$. It is the $q = 2$ case, and it feeds the construction of a formally smooth centred subalgebra used in the semistable-model analysis of the Igusa and supersingular charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_valuationSubring_localization_chartAlg_of_not_mem_descent_of_eq_two
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
    (𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S)) (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (hϖ : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S) ϖ₀ ∉ 𝔭) :
    ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S), c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀) := by sorry
