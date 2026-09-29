-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_chartAlgFin_descent
-- name    : ModularCurve.FullLevel.exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_chartAlgFin_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/2d4ef3b0-71cd-5b7a-a777-87a04d8988d8
-- title:
--   Descended chart ring inside the Drinfeld ring, centre maximal
-- statement:
--   Fix a prime $q\ge 5$, a nonzero level $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular set), let $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant-reduction datum for $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in that reduced field (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map with kernel the maximal ideal, compatibility with $A$, and a degree- and divisor-compatible place map), whose residue is computed coefficientwise on Laurent series with coefficients in $A$ ($hR_0$). Further data: $\pi\in A\cap K_0$ with $\pi^{q^2-1}=q$; a primitive $q$-th root of unity index $\zeta$; families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to: $O_{\mathrm{Ig}}(\infty)$ consists of the quotients $x/y$ of Laurent series over $A$ with $y$ of nonzero reduction; each $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\infty)$ along some $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma\in\Gamma_0(M')$ reducing to $\ell$; $O_{\mathrm{Ig}}$ injective and permuted by all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$, $\gamma\in\Gamma_0(M')$; each $O_{\mathrm{SS}}(s)$ meets the constants exactly in $A$, is fixed by all such $\mathrm{levelAutBar}$, contains an element $t$ with $t-a$ a unit for every $a\in A$, and, for $f\in R_0.\mathrm{integers}$ of nonnegative order wherever $j$ has nonnegative order and with $R_0$-residue in the valuation ring of $s$, contains the image of $f$ and has $f-a$ in its maximal ideal whenever $\mathrm{residue}\,a$ equals the value of $R_0.\mathrm{residue}\,f$ at $s$. Finally let $K_0\subseteq\overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$, let $A_0$ be a henselian discrete valuation domain with an injective local ring homomorphism $\iota:A_0\to A$ whose image is $A\cap K_0$ and which is residually surjective, let $\varpi_0$ generate the maximal ideal of $A_0$ with $\iota\varpi_0=\pi$, let $F_0$ be the subfield of $\mathrm{fieldBar}\,q\,M'$ of series all of whose Laurent coefficients lie in $K_0$, assume the image $\hat\jmath$ of $j$ lies in $F_0$ and is nonzero, and let the $A_0$-algebra structure on $F_0$ be the one induced by $\iota$. Then for every $s\in W$: every element of $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$, the $A_0$-subalgebra of elements of $F_0$ integral over $A_0[\hat\jmath]$, lies in $O_{\mathrm{SS}}(s)$, and there is a maximal ideal $\mathfrak n_s$ of that chart algebra containing the image of $\varpi_0$ and consisting exactly of those $g$ whose image in $\mathrm{fieldBar}\,q\,M'$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$.
--
--   This is the statement that a supersingular (Drinfeld) valuation ring of the geometric full-level function field dominates the descended Igusa chart algebra over the henselian base $A_0$, and that its centre on that algebra is a closed point lying over the uniformiser $\varpi_0$ — the algebraic form of the fact that the supersingular points of the Igusa model are closed points at which $j$ reduces to a constant. It feeds the uniqueness refinement of this centre and the comparison of nonunits of the Igusa ring with the Drinfeld maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_chartAlgFin_descent.lean

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

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open ModularCurve.FullLevel
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_chartAlgFin_descent
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
    (s : ↥W) :
    (∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s) ∧
    ∃ 𝔫s : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      𝔫s.IsMaximal ∧
      algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫s ∧
      (∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫s ↔
        ∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) := by sorry
