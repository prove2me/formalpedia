-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_unique_chartAlgFin_descent
-- name    : ModularCurve.FullLevel.exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_unique_chartAlgFin_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/1de04f6a-83dd-57c1-9192-e62845c34a09
-- title:
--   Unique maximal ideal over a supersingular place, descended chart
-- statement:
--   Fix a prime $q \ge 5$, a nonzero level $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ (places being valuation subrings containing the base field, proper and with principal ideals) whose members are exactly the supersingular ones: rational, satisfying `IsAffineGeomPlace`, and with value at `jGeomGen` in `ssJSet q`. Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a `ConstantReduction` of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ (a valuation subring of integers with a surjective residue homomorphism of kernel the maximal ideal, compatible with $A$ and with orders of places), assumed to compute coefficientwise reduction of Laurent series with coefficients in $A$. Further data: $\pi \in A$ with $\pi^{q^2-1} = q$; an index $\zeta$ of a primitive $q$-th root of unity; families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to: the quotient description of $O_{\mathrm{Ig}}(\infty)$ by Laurent series over $A$ with nonzero reduced denominator, transitivity of $\Gamma_0(M')$ on the $O_{\mathrm{Ig}}(\ell)$ through pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$, injectivity of $O_{\mathrm{Ig}}$, permutation of the family by all such pullbacks; and for $O_{\mathrm{SS}}$: contraction to $A$ on constants, stability under all pullbacks $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$, existence for each $s$ of $t \in O_{\mathrm{SS}}\,s$ with $t - a$ a unit for every $a \in A$, and the compatibility $hSS\_over$: for $f$ in the integers of $R_0$ regular at every place where the image of `jq` is regular and with $R_0$-residue in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{SS}}\,s$, and $f - a$ lies in its maximal ideal whenever the residue of $a \in A$ is the value at $s$ of that residue. The descent data are: a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$; a henselian discrete valuation domain $A_0$ with an injective local homomorphism $\iota : A_0 \to A$ whose image is $A \cap K_0$ and with $\mathrm{residue} \circ \iota$ surjective onto $\mathrm{ResidueField}\,A$; a uniformiser $\varpi_0$ of $A_0$ with $\iota\varpi_0 = \pi$; the subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ of elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of `jq`, which is nonzero, together with an $A_0$-algebra structure on $F_0$ induced by $\iota$. Then, for each $s \in W$, the chart algebra $\mathrm{TwoChartIntegralModel.chartAlgFin}\,A_0\,F_0\,\hat\jmath$ of elements of $F_0$ integral over $A_0[\hat\jmath]$ has a maximal ideal $\mathfrak n_s$ containing the image of $\varpi_0$ such that $g \in \mathfrak n_s$ precisely when the image of $g$ in $\mathrm{fieldBar}\,q\,M'$ lies in the maximal ideal of $O_{\mathrm{SS}}\,s$, and $\mathfrak n_s$ is the only maximal ideal $\mathfrak n$ containing the image of $\varpi_0$ with the property that $g \in \mathfrak n$ whenever the image of $g$ equals $f - \iota a$ for some $f$ in the integers of $R_0$ regular where the image of `jq` is, with $R_0$-residue in the valuation subring of $s$, and some $a \in A_0$ whose residue is the value at $s$ of that residue.
--
--   This is the statement that over each supersingular place of the reduced level-$M'$ floor there is a single closed point of the descended two-chart Igusa-level model, namely the contraction of the Drinfeld valuation ring, in the form of a uniqueness assertion for maximal ideals of the $\hat\jmath$-finite chart algebra over $A_0$. It is used in the construction of the semistable model of the full-level modular curve, where the points lying over supersingular $j$-invariants must be identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_unique_chartAlgFin_descent.lean

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

theorem ModularCurve.FullLevel.exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_unique_chartAlgFin_descent
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
    ∃ 𝔫s : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      𝔫s.IsMaximal ∧
      algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫s ∧

      (∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫s ↔
        ∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) ∧

      (∀ 𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), 𝔫.IsMaximal → algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫 →
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
              g ∈ 𝔫) →
        𝔫 = 𝔫s) := by sorry
