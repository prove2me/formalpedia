-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_three
-- name    : ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/08c87213-47ca-5616-b5e4-bef29502daa7
-- title:
--   Rational affine floor place below a maximal ideal of the jmatĥ-chart (q=3)
-- statement:
--   Fix a prime $q$ with $q=3$, a level $M'\neq 0$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\kappa,M')$ over $\kappa=\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places, i.e. the rational places $w$ (the map $\kappa\to w$'s residue field being surjective) with $\jmath$ and its $M'$-expansion in $w$'s valuation ring and $w(\jmath)\in\mathrm{ssJSet}\,q\,\kappa$. Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of the former along $A$ with values in $\mathrm{modularFunctionFieldC}(\kappa,M')$ whose residue map is computed coefficientwise on Laurent series with coefficients in $A$. Further data: $\pi\in A$ with $\pi^{q^2-1}=q$, a primitive $q$-th root of unity $\zeta$, families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to: the Gauss-ring description of $O_{\mathrm{Ig}}(\infty)$ as the set of $f$ with $fy=x$ for Laurent series $x,y$ over $A$ with $y$ not reducing to $0$; transitivity of the $\Gamma_0(M')$-automorphisms $\mathrm{levelAutBar}$ on the $O_{\mathrm{Ig}}$, injectivity of $O_{\mathrm{Ig}}$, permutation of the $O_{\mathrm{Ig}}$ by all $\mathrm{levelAutBar}\,\zeta'\,\gamma$; for each $s\in W$, $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ in $A$, is $\mathrm{levelAutBar}$-invariant, contains an element $t$ with $t-a$ a unit for all $a\in A$, and receives the $R_0$-integral floor functions regular where $\hat\jmath$ is and at $s$, with the correct reduction (subtracting a constant $a$ with $\mathrm{res}(a)=\bar f(s)$ lands in the maximal ideal). Descent data: a subfield $K_0\subseteq\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$; a henselian discrete valuation domain $A_0$ with an injective local map $\iota:A_0\to A$ whose image is $A\cap K_0$ and which is residually surjective, with uniformiser $\varpi_0$ satisfying $\iota\varpi_0=\pi$; the subfield $F_0\subseteq\mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of $j_q$, which is nonzero, with an $A_0$-algebra structure on $F_0$ induced by $\iota$. Finally let $\mathfrak n$ be a maximal ideal of $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$, the algebra of elements of $F_0$ integral over $A_0[\hat\jmath]$, with $\varpi_0\in\mathfrak n$. The conclusion: there is a place $s$ of $\mathrm{modularFunctionFieldC}(\kappa,M')$ over $\kappa$ which is rational and affine-geometric ($\jmath$ and its $M'$-expansion lie in its valuation ring) and lies under $\mathfrak n$ in the following two senses. First, for every $f$ in $R_0$'s ring of integers having non-negative order at every place where $\hat\jmath$ does, whose $R_0$-residue lies in the valuation ring of $s$, and every $a\in A_0$ with $\mathrm{res}(\iota a)=s.\mathrm{evalAt}$ of that residue, any $g\in\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$ whose image in $\mathrm{fieldBar}\,q\,M'$ equals $f-\iota a$ lies in $\mathfrak n$. Second, for every $a\in A_0$ with $\mathrm{res}(\iota a)=s.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M')$, the element $\mathrm{jChartFin}-a$ lies in $\mathfrak n$.
--
--   This is the dictionary step that converts a closed point of the special fibre of the descended two-chart integral model (a maximal ideal of the $\hat\jmath$-finite chart containing the uniformiser) into a rational affine place of the reduced level-$M'$ modular function field over the residue field, together with the statement that the two are compatible on floor functions and on $\hat\jmath$ itself; it is the $q=3$ case, whose Igusa leg requires no rigidity guard. It is used in the construction of supersingular places of the reduced floor attached to such closed points in the semistable-covering analysis of $X_H(q^2M')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_three
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
