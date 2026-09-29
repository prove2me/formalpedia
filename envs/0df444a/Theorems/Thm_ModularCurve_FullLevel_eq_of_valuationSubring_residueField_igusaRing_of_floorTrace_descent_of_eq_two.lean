-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_two
-- name    : ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/cd864653-e794-5f56-8629-79618780d9f5
-- title:
--   Uniqueness of Igusa-component valuation ring reading a supersingular place (q=2)
-- statement:
--   Fix a prime $q$ with $q = 2$ and a level $M'\ge 1$ with $q \nmid M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ belongs to the non-units of $A$ (`A.LiesOverPrime q`), and a finite set $W$ of places of the field $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over the residue field of $A$; the hypothesis `hW` says that $W$ consists exactly of the supersingular places, i.e. of those places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}$ of the geometric $j$-generator lying in the supersingular $j$-set for $q$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing $K$, different from $F$, and a principal ideal ring, $P.\mathrm{ord}$ denotes the associated normalised order function, and $P.\mathrm{evalAt}$ the evaluation of an element at a rational place.
--
--   Further data: an inclusion `hle` of the geometric full-level field $\mathrm{modularFunctionFieldBar}\,M'$ (the base change to $\overline{\mathbb Q}$, inside Laurent series, of the full modular function field of level $M'$) into $\mathrm{fieldBar}\,q\,M'$, the geometric function field of the $\Gamma_H$-curve of level $q^2M'$ for the subgroup $H = \ker(\mathrm{ZMod}(q^2M')^\times \to \mathrm{ZMod}(q)^\times)$; a constant reduction $R_0$ of $\mathrm{modularFunctionFieldBar}\,M'$ with respect to $A$, with values in $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ — that is, a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto the target field with kernel the maximal ideal, a map on places preserving degrees, compatibility with $A$ and with $\mathrm{residue}$ on constants, a scaling axiom, and compatibility of divisors with the place map — together with the hypothesis `hR₀`, which says that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$, this element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is, as a Laurent series over $\mathrm{ResidueField}\,A$, the coefficientwise reduction of $y$; an element $\pi \in A$ with $\pi^{q^2-1} = q$; a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`); and two families of valuation subrings of $\mathrm{fieldBar}\,q\,M'$, namely $O_{\mathrm{Ig}}$ indexed by $\mathbb P^1(\mathrm{ZMod}\,q)$ and $O_{\mathrm{SS}}$ indexed by $W$.
--
--   The Igusa group of hypotheses: `hIg_inf` characterises $O_{\mathrm{Ig}}(\infty)$ as the set of $f$ for which there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ non-zero and $f \cdot y = x$ as Laurent series over $\overline{\mathbb Q}$; `hIg` provides, for each line $\ell$, a matrix $\gamma \in \Gamma_0(M')$ whose reduction modulo $q$ carries $\infty$ to $\ell$ and with $O_{\mathrm{Ig}}(\ell)$ equal to the preimage of $O_{\mathrm{Ig}}(\infty)$ under $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; `hIg_inj` asserts injectivity of $\ell \mapsto O_{\mathrm{Ig}}(\ell)$; `hIg_perm` asserts that for every primitive root $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the preimages of the $O_{\mathrm{Ig}}(\ell)$ under $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permute the family.
--
--   The supersingular group of hypotheses: `hSS_A` says that for each $s \in W$ and each $x \in \overline{\mathbb Q}$ the image of $x$ lies in $O_{\mathrm{SS}}(s)$ exactly when $x \in A$; `hSS_over` says that for $s \in W$ and $f \in R_0.\mathrm{integers}$ which is regular wherever $\hat\jmath$ is (that is, $0 \le P.\mathrm{ord}(f)$ at every place $P$ at which $0 \le P.\mathrm{ord}$ of the element $\hat\jmath$ of $\mathrm{modularFunctionFieldBar}\,M'$ given by the coefficientwise image of $j_q$) and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{SS}}(s)$, and moreover for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of the image of $f$ and the image of $a$ lies in $O_{\mathrm{SS}}(s)$ and in its maximal ideal; `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is its own preimage under $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$; `hSS_tr` provides for each $s$ an element $t \in O_{\mathrm{SS}}(s)$ such that $t - a$ lies in $O_{\mathrm{SS}}(s)$ and is a unit there for every $a \in A$.
--
--   The descent data: a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}$ algebraic over $K_0$ and $\pi \in K_0$; a domain $A_0$ which is a discrete valuation ring and a henselian local ring, an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ (`hιK₀`), with $\mathrm{residue} \circ \iota$ surjective onto the residue field of $A$ (`hres`), a uniformiser $\varpi_0$ generating the maximal ideal of $A_0$ (`hϖ₀`) with $\iota(\varpi_0) = \pi$ (`hϖ₀π`); a subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that $\hat\jmath$ lies in $F_0$; an $A_0$-algebra structure on $F_0$ whose structure map agrees, by `hj₀`, with $\iota$ followed by $\overline{\mathbb Q} \to \mathrm{fieldBar}\,q\,M'$; and the requirement that $\hat\jmath \ne 0$ in $F_0$.
--
--   Finally, fix $s \in W$ and a line $\ell \in \mathbb P^1(\mathrm{ZMod}\,q)$, write $O_\ell$ for the preimage $O_{\mathrm{Ig}}(\ell) \cap F_0$ of $O_{\mathrm{Ig}}(\ell)$ under the inclusion of $F_0$, and let $W_1, W_2$ be valuation subrings of the residue field of the local ring $O_\ell$, both assumed different from the whole residue field (`hW₁`, `hW₂`). Let $C$ denote the finite chart algebra $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$, i.e. the $A_0$-subalgebra of $F_0$ of elements integral over the $A_0$-subalgebra generated by $\hat\jmath$. The hypotheses `hC₁` and `hC₂` require that for every $g \in C$ lying in $O_\ell$ the residue of $g$ belongs to $W_1$, respectively to $W_2$. The reading hypotheses `hread₁` and `hread₂` require, for $i = 1, 2$: for every $f \in R_0.\mathrm{integers}$ regular wherever $\hat\jmath$ is (in the sense above) and with $R_0$-residue in the valuation subring of $s$, for every $a \in A_0$ with $\mathrm{residue}_A(\iota a) = s.\mathrm{evalAt}$ of that $R_0$-residue, and for every $g \in C$ lying in $O_\ell$ such that $g$ equals the image of $f$ minus the image of $\iota a$ in $\mathrm{fieldBar}\,q\,M'$, the residue of $g$ in the residue field of $O_\ell$ is a non-unit of $W_i$.
--
--   Under these hypotheses the conclusion is the single equality $W_1 = W_2$.
--
--   This is the $q = 2$ case of the uniqueness statement for the valuation ring on an Igusa component of the descended two-chart model that both dominates the residues of the finite chart algebra and reads off a prescribed supersingular place of the reduced level-$M'$ function field; at $q = 2$ the Igusa covering of the relevant branch is trivial, so the conditions involved degenerate accordingly. It is used in the construction of the semistable covering of the modular curve, by [`ModularCurve.FullLevel.eq_of_isMaximal_of_mem_nonunits_igusaRing_of_floorTrace_chartAlgFin_descent_of_eq_two`](thm.html#ModularCurve.FullLevel.eq_of_isMaximal_of_mem_nonunits_igusaRing_of_floorTrace_chartAlgFin_descent_of_eq_two) and by [`ModularCurve.FullLevel.eq_of_le_gaussRing_of_forall_isIntegral_mem_maximalIdeal_drinfeldRing_mem_nonunits_descent_of_eq_two`](thm.html#ModularCurve.FullLevel.eq_of_le_gaussRing_of_forall_isIntegral_mem_maximalIdeal_drinfeldRing_mem_nonunits_descent_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_two.lean

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

theorem ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_two
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
    (s : ↥W) (ℓ : CuspidalType.ProjLine q)
    (W₁ W₂ : ValuationSubring (IsLocalRing.ResidueField ↥((OIg ℓ).comap F₀.subtype)))
    (hW₁ : W₁ ≠ ⊤) (hW₂ : W₂ ≠ ⊤)
    (hC₁ : ∀ (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ ((OIg ℓ).comap F₀.subtype)), IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩ ∈ W₁)
    (hC₂ : ∀ (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ ((OIg ℓ).comap F₀.subtype)), IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩ ∈ W₂)
    (hread₁ : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A₀, residue A (ι a) =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∀ (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ ((OIg ℓ).comap F₀.subtype)), ((g : ↥F₀) : ↥(fieldBar q M')) =
                (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
              IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩ ∈ W₁.nonunits))
    (hread₂ : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A₀, residue A (ι a) =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∀ (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ ((OIg ℓ).comap F₀.subtype)), ((g : ↥F₀) : ↥(fieldBar q M')) =
                (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
              IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩ ∈ W₂.nonunits)) :
    W₁ = W₂ := by sorry
