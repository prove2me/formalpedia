-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_three
-- name    : ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/4b2f6cc7-0bd2-5536-bb6c-4e05c29225ba
-- title:
--   Uniqueness of the Igusa-component valuation ring reading s (q=3)
-- statement:
--   Fix a prime $q$ with $q=3$ and a nonzero level $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a non-unit of $A$. Let $W$ be a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$, assumed by `hW` to consist of exactly the supersingular places `ssPlaces q M' (ResidueField A)` (those places that are rational, affine geometric, and at which the value of the geometric $j$-invariant is supersingular). Let `hle` be the inclusion $\overline{\mathbb Q}\cdot F(\Gamma(M')\text{-full level}) =$ `modularFunctionFieldBar M'` $\le$ `fieldBar q M'`, the latter being the base change to $\overline{\mathbb Q}$ of the function field of the level-$\Gamma_H(q^2M')$ curve for $H =$ `levelH q M'`. Let $R_0$ be a `ConstantReduction` of `modularFunctionFieldBar M'` over $A$ with values in `modularFunctionFieldC (ResidueField A) M'` — that is, a valuation subring $R_0.\mathrm{integers}$ of the former, a surjective residue map to the latter with kernel the maximal ideal, compatible with $A$ and with reduction of constants, together with a map on places preserving degrees and order functions — and let `hR₀` require that for every Laurent series $y$ over $A$ whose image in `LaurentSeries (AlgebraicClosure ℚ)` lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is, as a Laurent series over the residue field of $A$, the coefficientwise reduction of $y$. Let $\pi \in \overline{\mathbb Q}$ satisfy $\pi^{q^2-1} = q$ and $\pi \in A$, let $\zeta$ be an element of `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb Q}$), and let $O_{\mathrm{Ig}} =$ `OIg` and $O_{\mathrm{ss}} =$ `OSS` be families of valuation subrings of `fieldBar q M'` indexed respectively by the projective line $\mathbb P^1(\mathbb Z/q)$ and by $W$.
--
--   The Igusa data are four hypotheses: `hIg_inf` describes $O_{\mathrm{Ig}}$ at the line `lineInfty q` as the set of $f$ admitting Laurent series $x, y$ over $A$ with $y$ of nonzero coefficientwise reduction and $f \cdot y = x$ after pushing forward to $\overline{\mathbb Q}$; `hIg` provides, for each line $\ell$, some $\gamma \in \Gamma_0(M')$ whose reduction mod $q$ carries `lineInfty q` to $\ell$ and for which $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\mathrm{lineInfty})$ along the automorphism `levelAutBar q M' ζ γ`; `hIg_inj` asserts injectivity of $\ell \mapsto O_{\mathrm{Ig}}(\ell)$; and `hIg_perm` asserts that for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pullbacks along `levelAutBar q M' ζ' γ` permute the family, i.e. agree with $O_{\mathrm{Ig}} \circ \sigma$ for some permutation $\sigma$ of $\mathbb P^1(\mathbb Z/q)$.
--
--   The supersingular data are four hypotheses. `hSS_A` says that for each $s$ and each $x \in \overline{\mathbb Q}$, the image of $x$ in `fieldBar q M'` lies in $O_{\mathrm{ss}}(s)$ if and only if $x \in A$. `hSS_over` says that for $s \in W$ and $f \in R_0.\mathrm{integers}$ such that $f$ has nonnegative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the base-changed $q$-expansion $\hat\jmath$ of the modular invariant has nonnegative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$: the image of $f$ in `fieldBar q M'` lies in $O_{\mathrm{ss}}(s)$, and for every $a \in A$ whose residue in the residue field of $A$ equals the value at $s$ of the $R_0$-residue of $f$, the difference of that image and the image of $a$ lies in $O_{\mathrm{ss}}(s)$ and in its maximal ideal. `hSS_fix` says each $O_{\mathrm{ss}}(s)$ is stable under pullback along `levelAutBar q M' ζ' γ` for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$. `hSS_tr` provides, for each $s$, an element $t \in O_{\mathrm{ss}}(s)$ such that for every $a \in A$ the difference $t - a$ lies in $O_{\mathrm{ss}}(s)$ and is a unit there.
--
--   The descent data are as follows: a subfield $K_0 \subseteq \overline{\mathbb Q}$ over which $\overline{\mathbb Q}$ is algebraic and which contains $\pi$; a henselian discrete valuation domain $A_0$ with an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ (hypothesis `hιK₀`), with residue map $A_0 \to \mathrm{ResidueField}\,A$ surjective (`hres`), with a generator $\varpi_0$ of the maximal ideal of $A_0$ (`hϖ₀`) whose image in $\overline{\mathbb Q}$ is $\pi$ (`hϖ₀π`); a subfield $F_0$ of `fieldBar q M'` characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that the image of $\hat\jmath$ in `fieldBar q M'` lies in $F_0$, this element being nonzero; and an $A_0$-algebra structure on $F_0$ which by `hj₀` is induced by $\iota$ followed by the structure map $\overline{\mathbb Q} \to$ `fieldBar q M'`.
--
--   Finally fix $s \in W$ and a line $\ell \in \mathbb P^1(\mathbb Z/q)$, write $O_\ell$ for the valuation subring $(O_{\mathrm{Ig}}(\ell))$ pulled back to $F_0$, and let $W_1, W_2$ be valuation subrings of the residue field of $O_\ell$, both different from $\top$ (`hW₁`, `hW₂`). Let $C$ denote `TwoChartIntegralModel.chartAlgFin A₀ F₀ ĵ`, the $A_0$-subalgebra of $F_0$ of elements integral over $A_0[\hat\jmath]$. The hypotheses `hC₁` and `hC₂` require that for every $g \in C$ lying in $O_\ell$, the residue of $g$ in the residue field of $O_\ell$ belongs to $W_1$, respectively to $W_2$. The hypotheses `hread₁` and `hread₂` are the reading conditions: for every $f \in R_0.\mathrm{integers}$ which has nonnegative order at every place at which $\hat\jmath$ has nonnegative order and whose $R_0$-residue lies in the valuation subring of $s$, for every $a \in A_0$ with $\iota a$ reducing to the value at $s$ of that $R_0$-residue, and for every $g \in C$ lying in $O_\ell$ whose image in `fieldBar q M'` equals the image of $f$ minus the image of $\iota a$, the residue of $g$ in the residue field of $O_\ell$ is a non-unit of $W_1$, respectively of $W_2$.
--
--   Under these hypotheses, $W_1 = W_2$.
--
--   This is the uniqueness step for the valuation ring cut out on the residue field of an Igusa component of the semistable model at $q$: the requirement of containing all chart residues and of reading the supersingular place $s$ (sending the relevant differences $f - a$ into the non-units) pins the ring down, in the descended situation over the henselian base $A_0$ and the coefficient field $K_0$. It is the $q = 3$ case, companion to the statement for $q \ge 5$, and it is used in the two subsequent descent statements [`ModularCurve.FullLevel.eq_of_isMaximal_of_mem_nonunits_igusaRing_of_floorTrace_chartAlgFin_descent_of_eq_three`](thm.html#ModularCurve.FullLevel.eq_of_isMaximal_of_mem_nonunits_igusaRing_of_floorTrace_chartAlgFin_descent_of_eq_three) and [`ModularCurve.FullLevel.eq_of_le_gaussRing_of_forall_isIntegral_mem_maximalIdeal_drinfeldRing_mem_nonunits_descent_of_eq_three`](thm.html#ModularCurve.FullLevel.eq_of_le_gaussRing_of_forall_isIntegral_mem_maximalIdeal_drinfeldRing_mem_nonunits_descent_of_eq_three), which identify the local rings of the two-chart integral model at the crossing points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_three
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
