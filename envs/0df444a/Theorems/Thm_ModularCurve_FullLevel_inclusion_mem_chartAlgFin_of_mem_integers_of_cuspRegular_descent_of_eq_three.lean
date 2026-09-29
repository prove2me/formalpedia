-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_inclusion_mem_chartAlgFin_of_mem_integers_of_cuspRegular_descent_of_eq_three
-- name    : ModularCurve.FullLevel.inclusion_mem_chartAlgFin_of_mem_integers_of_cuspRegular_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/a56e67c4-b275-5a7a-a036-8e7175e71336
-- title:
--   Cusp-regular R₀-integral functions lie in the jmatĥ-chart, q=3
-- statement:
--   Fix a prime $q$ with $q=3$ and a nonzero level $M'$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places, i.e. the rational affine geometric places whose value at the geometric $j$-generator lies in the supersingular set for $q$. Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of the base-changed full level-$M'$ function field along $A$ whose integers contain every element given by a Laurent series with coefficients in $A$, with residue computed coefficientwise (hypothesis `hR₀`). Further data: an element $\pi \in A$ with $\pi^{q^2-1}=q$, an index $\zeta$ of primitive $q$-th roots of unity, families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb Z/q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to the Igusa-chart hypotheses (`hIg_inf`, `hIg`, `hIg_inj`, `hIg_perm`: the ring at $\ell = \infty$ is described by quotients of Laurent series with $A$-coefficients and denominator of nonzero reduction, every $\ell$ is reached from $\infty$ by a $\Gamma_0(M')$-matrix reduced mod $q$ with $O_{\mathrm{Ig}}(\ell)$ the corresponding pullback under `levelAutBar`, $O_{\mathrm{Ig}}$ is injective, and $\Gamma_0(M')$ permutes the $O_{\mathrm{Ig}}(\ell)$) and the supersingular-chart hypotheses (`hSS_A`, `hSS_over`, `hSS_fix`, `hSS_tr`: each $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ exactly in $A$, reads off $R_0$-residues at $s$ on cusp-regular $R_0$-integral elements together with their Teichmüller approximations modulo the maximal ideal, is `levelAutBar`-invariant, and admits an element $t$ with $t-a$ a unit for every $a \in A$), all summarised here. Descent data: a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$; a henselian discrete valuation domain $A_0$ with an injective local homomorphism $\iota : A_0 \to A$ whose image is $A \cap K_0$, inducing a surjection onto the residue field of $A$, and with a uniformiser $\varpi_0$ satisfying $\iota(\varpi_0)=\pi$; a subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ consisting precisely of those elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of $j$ and an $A_0$-algebra whose structure map is $\iota$ followed by the inclusion of $\overline{\mathbb Q}$, with $\hat\jmath \ne 0$. Finally let $g$ be a Laurent series over $\mathbb Q$ lying in the full level-$M'$ function field, such that its base change lies in the integers of $R_0$, such that $\mathrm{ord}_P(g) \ge 0$ at every place $P$ of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which $\mathrm{ord}_P(j) \ge 0$, and whose image in $\mathrm{fieldBar}\,q\,M'$ lies in $F_0$. Then that image, viewed in $F_0$, is integral over $A_0[\hat\jmath]$, that is, it belongs to $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$.
--
--   This is the chart-membership step for the finite ($\hat\jmath$-integral) chart of the two-chart integral model of the full-level curve after descent to the small base $A_0$, in the case $q=3$: the modular functions one wishes to use as coordinates are shown to be integral over $A_0[\hat\jmath]$. It is used in the statement that places of the descended field read off supersingular places through the Igusa rings, [`ModularCurve.FullLevel.forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three`](thm.html#ModularCurve.FullLevel.forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_inclusion_mem_chartAlgFin_of_mem_integers_of_cuspRegular_descent_of_eq_three.lean

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

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.inclusion_mem_chartAlgFin_of_mem_integers_of_cuspRegular_descent_of_eq_three
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
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')))
    (hF : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) g,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀) :
    (⟨_, hF⟩ : ↥F₀) ∈ TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) := by sorry
