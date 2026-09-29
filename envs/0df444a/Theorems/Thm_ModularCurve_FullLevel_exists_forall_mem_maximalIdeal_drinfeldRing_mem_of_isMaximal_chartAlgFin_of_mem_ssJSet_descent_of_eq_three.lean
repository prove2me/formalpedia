-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_forall_mem_maximalIdeal_drinfeldRing_mem_of_isMaximal_chartAlgFin_of_mem_ssJSet_descent_of_eq_three
-- name    : ModularCurve.FullLevel.exists_forall_mem_maximalIdeal_drinfeldRing_mem_of_isMaximal_chartAlgFin_of_mem_ssJSet_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/df267379-d183-52d0-8114-cbf0979e71ad
-- title:
--   Drinfeld centre of a supersingular special point, q=3
-- statement:
--   Fix the prime $q$ with $q = 3$, a level $M'\neq 0$ with $q\nmid M'$, and a valuation subring $A\subseteq\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ whose members are exactly the supersingular places (rational, affine geometric, with supersingular value of the generic $j$-invariant), let $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ via `hle`, and let $R_0$ be a `ConstantReduction` of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in that residue function field, compatible with coefficientwise reduction of Laurent series over $A$ (`hR₀`). Further data: $\pi\in A$ with $\pi^{q^2-1}=q$, an index $\zeta$ of primitive $q$-th roots of unity, and families $O_{\mathrm{Ig}}$ over $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}$ over $W$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ subject to the Igusa axioms (description of $O_{\mathrm{Ig}}(\infty)$ by quotients of Laurent series over $A$, $\Gamma_0(M')$-transitivity and permutation behaviour under `levelAutBar`, injectivity) and the Drinfeld axioms (contraction to $A$ on $\overline{\mathbb Q}$, the specialisation property `hSS_over` relating $R_0$-residues at $s$ to membership and to maximal-ideal congruences, invariance under `levelAutBar`, and existence of a parameter $t$ with $t-a$ a unit for all $a\in A$), summarised here. Finally: a subfield $K_0\subseteq\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$; a henselian discrete valuation ring $A_0$ with an injective local homomorphism $\iota:A_0\to A$ whose image in $\overline{\mathbb Q}$ is $A\cap K_0$, with surjective induced residue map, and a uniformiser $\varpi_0$ with $\iota\varpi_0=\pi$; the subfield $F_0\subseteq\mathrm{fieldBar}\,q\,M'$ of elements all of whose Laurent coefficients lie in $K_0$, which contains the image $\hat\jmath$ of $j$, together with an $A_0$-algebra structure on $F_0$ agreeing with $\iota$; a maximal ideal $\mathfrak n$ of $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$ (the elements of $F_0$ integral over $A_0[\hat\jmath]$) containing $\varpi_0$; and a ring homomorphism $\varphi$ from that chart algebra to an algebraically closed field $\Omega$ of characteristic $q$ with kernel $\mathfrak n$ and $\varphi(\hat\jmath)$ a supersingular $j$-value. Then there is $s\in W$ such that every $g$ in the chart algebra whose image in $\mathrm{fieldBar}\,q\,M'$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$ lies in $\mathfrak n$.
--
--   This is the node, or Drinfeld, branch of the dichotomy for closed points of characteristic $q$ on the descended two-chart integral model of the full-level modular curve: a special point whose $j$-value is supersingular is dominated by one of the Drinfeld valuation rings $O_{\mathrm{SS}}(s)$. It is the case $q = 3$, and it feeds the statement that near such a point the model is either formally smooth over a centred subalgebra or else all relevant elements are non-units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_forall_mem_maximalIdeal_drinfeldRing_mem_of_isMaximal_chartAlgFin_of_mem_ssJSet_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_forall_mem_maximalIdeal_drinfeldRing_mem_of_isMaximal_chartAlgFin_of_mem_ssJSet_descent_of_eq_three
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
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* Ω) (hφ : RingHom.ker φ = 𝔫)
    (hss : φ (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ∈ ModularCurve.ssJSet q Ω) :
    ∃ s : ↥W, ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) → g ∈ 𝔫 := by sorry
