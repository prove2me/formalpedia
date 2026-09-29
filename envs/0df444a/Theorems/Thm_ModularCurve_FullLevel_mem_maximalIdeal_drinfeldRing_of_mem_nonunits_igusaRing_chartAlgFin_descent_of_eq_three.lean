-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent_of_eq_three
-- name    : ModularCurve.FullLevel.mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/c6ff4fee-5af1-5428-aadb-085a1fe16fe5
-- title:
--   Igusa non-units lie in each Drinfeld maximal ideal (q=3)
-- statement:
--   Fix a prime $q$ with $q = 3$, a nonzero level $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ whose members are exactly the supersingular places (rational, affine geometric, with $\mathrm{evalAt}$ of the geometric $j$-generator in the supersingular $j$-set), let $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ via `hle`, and let $R_0$ be a `ConstantReduction` of $A$ from the geometric full-level field to that residual function field, compatible (`hR₀`) with coefficientwise reduction of Laurent series over $A$. Further data: an element $\pi \in A$ with $\pi^{q^2-1} = q$; an index $\zeta$ in $\mathrm{Idx}\,q$ (a primitive $q$-th root of unity); Igusa valuation subrings $O_{\mathrm{Ig}}(\ell)$ of $\mathrm{fieldBar}\,q\,M'$ indexed by $\ell \in \mathbb P^1(\mathbb F_q)$, and Drinfeld valuation subrings $O_{\mathrm{SS}}(s)$ indexed by $s \in W$. The hypotheses on these rings are: $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ consists of the ratios of coefficient-images of Laurent series over $A$ with denominator of nonzero reduction; every $\ell$ is obtained from $\mathrm{lineInfty}\,q$ by some $\gamma \in \Gamma_0(M')$, in the sense that $\mathrm{redQ}\,q\,\gamma$ carries $\mathrm{lineInfty}\,q$ to $\ell$ and $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; $O_{\mathrm{Ig}}$ is injective and its values are permuted by pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$; each $O_{\mathrm{SS}}(s)$ meets the constants $\overline{\mathbb Q}$ exactly in $A$, is invariant under all these pullbacks, and carries an element $t$ such that $t - a$ is a unit for every $a \in A$; and each $O_{\mathrm{SS}}(s)$ is compatible with $R_0$ and $s$: for $f$ in $R_0$'s integers with $\mathrm{ord}_P f \ge 0$ at every place where the order of the image of $\mathrm{jq}$ is $\ge 0$, and with $R_0$-residue in the valuation subring of $s$, the image of $f$ lies in $O_{\mathrm{SS}}(s)$ and, for each $a \in A$ whose residue equals the value of that residue at $s$, the difference of the image of $f$ and $a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$. Finally, descent data: a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$; a henselian discrete valuation domain $A_0$ with an injective local ring homomorphism $\iota : A_0 \to A$ whose image is $A \cap K_0$, with $\mathrm{residue} \circ \iota$ surjective onto the residue field of $A$ and with a generator $\varpi_0$ of the maximal ideal satisfying $\iota(\varpi_0) = \pi$; the subfield $F_0 \subseteq \mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of $\mathrm{jq}$, which is nonzero, with an $A_0$-algebra structure on $F_0$ induced by $\iota$. Then for every $s \in W$, every $\ell \in \mathbb P^1(\mathbb F_q)$ and every $g$ in $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$, the subalgebra of elements of $F_0$ integral over $A_0[\hat\jmath]$, whose image in $\mathrm{fieldBar}\,q\,M'$ is a non-unit of $O_{\mathrm{Ig}}(\ell)$: that image lies in $O_{\mathrm{SS}}(s)$ and, as an element of $O_{\mathrm{SS}}(s)$, lies in its maximal ideal.
--
--   This is the $q = 3$ case of the assertion that, on the descended finite chart of the two-chart integral model, every Igusa component passes through each contracted supersingular (Drinfeld) point: non-units of the Igusa ring attached to any line $\ell$ are non-units at every Drinfeld ring attached to a supersingular place. It feeds the statement identifying the maximal ideals of the Drinfeld rings on the finite chart of the descended model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent_of_eq_three
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
    (s : ↥W) (ℓ : CuspidalType.ProjLine q)
    (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits) :
    ∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s) := by sorry
