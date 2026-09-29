-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent
-- name    : ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/c39c1d86-b131-5850-a316-38a13e860b58
-- title:
--   Rational affine place below a maximal ideal of the chart
-- statement:
--   Fix a prime $q\ge 5$ and a level $M'\ne 0$ with $q\nmid M'$, a valuation subring $A\subseteq\overline{\mathbb Q}$ with $q$ a non-unit of $A$, residue field $\kappa=\kappa(A)$, and a finite set $W$ of places of the $q$-expansion function field $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ consisting exactly of the supersingular places (rational, with both $j$ and its $M'$-twin regular, and $j$-value in $\mathrm{ssJSet}\ q$). Assume $\mathrm{modularFunctionFieldBar}\ M'\le \mathrm{fieldBar}\ q\ M'$, and let $R_0$ be a constant reduction of the base-changed full-level field along $A$ whose residue map is computed coefficientwise on Laurent series with coefficients in $A$. Further data: $\pi\in A$ with $\pi^{q^2-1}=q$; an index $\zeta$ of primitive $q$-th roots of unity; families $O_{\mathrm{Ig}}$ over $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{ss}}$ over $W$ of valuation subrings of $\mathrm{fieldBar}\ q\ M'$, subject to the Igusa hypotheses (the ring at $\infty$ consists of the ratios $x/y$ of Laurent series over $A$ with $\bar y\ne0$, the family is transitive under $\Gamma_0(M')$ through `levelAutBar`, injective, and permuted by all these automorphisms) and the supersingular hypotheses ($O_{\mathrm{ss}}(s)$ meets the constants exactly in $A$, is invariant under `levelAutBar` for $\gamma\in\Gamma_0(M')$, admits an element $t$ with $t-a$ a unit for all $a\in A$, and for $f$ in $R_0$'s valuation ring which is regular wherever $j$ is and whose reduction lies in $s$, the image of $f$ lies in $O_{\mathrm{ss}}(s)$ and $f-a$ lies in its maximal ideal whenever $\bar a=\bar f(s)$). Descent data: a subfield $K_0\subseteq\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$; a henselian discrete valuation ring $A_0$ with an injective local homomorphism $\iota:A_0\to A$ whose image is $A\cap K_0$, inducing a surjection onto $\kappa$, with uniformiser $\varpi_0$ satisfying $\iota\varpi_0=\pi$; the subfield $F_0\subseteq\mathrm{fieldBar}\ q\ M'$ of elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of $j$ and nonzero there, with an $A_0$-algebra structure compatible with $\iota$; and a maximal ideal $\mathfrak n$ of $\mathrm{chartAlgFin}\ A_0\ F_0\ \hat\jmath$, the subalgebra of elements of $F_0$ integral over $A_0[\hat\jmath]$, containing the image of $\varpi_0$. Then there is a place $s$ of $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ which is rational (the structure map to its residue field is surjective) and affine geometric (both $j$ and its $M'$-twin lie in its valuation subring) such that: for every $f$ in $R_0$'s valuation ring with $\mathrm{ord}_P f\ge0$ at every place $P$ where $\mathrm{ord}_P j\ge 0$, whose reduction lies in the valuation subring of $s$, and every $a\in A_0$ with $\overline{\iota a}$ equal to the value at $s$ of that reduction, every $g$ in the chart algebra whose image in $\mathrm{fieldBar}\ q\ M'$ equals $f-\iota a$ lies in $\mathfrak n$; and for every $a\in A_0$ with $\overline{\iota a}$ the value of $j$ at $s$, $\hat\jmath-a$ lies in $\mathfrak n$.
--
--   This is the point-to-place half of the dictionary between closed points of the descended two-chart integral model of the full-level modular curve and places of the reduced level-$M'$ function field over $\kappa(A)$: a maximal ideal of the $\hat\jmath$-finite chart containing the uniformiser restricts to a rational affine place of the reduction, at which the specified functions take the prescribed values. It feeds the statement identifying, for maximal ideals whose $j$-value is supersingular, a supersingular place of the reduced floor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent.lean

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

theorem ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent
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
    (𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫 : 𝔫.IsMaximal)
    (hϖ : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫)
    :
    ∃ s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'),
      s.IsRational ∧ IsAffineGeomPlace (ResidueField A) M' s ∧

      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A₀, residue A (ι a) =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) =
                (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
              g ∈ 𝔫) ∧

      (∀ a : A₀, residue A (ι a) =
          s.evalAt (jGeomGen (ResidueField A) M') →
        TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a ∈ 𝔫) := by sorry
