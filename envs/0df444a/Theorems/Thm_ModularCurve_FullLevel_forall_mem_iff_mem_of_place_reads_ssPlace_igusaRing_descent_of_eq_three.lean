-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three
-- name    : ModularCurve.FullLevel.forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/b0e16554-39c7-5d2e-bd97-f6beeb2a4ca8
-- title:
--   Igusa-chart reading of a supersingular place, q=3
-- statement:
--   Throughout, $q$ is a prime with $q = 3$, $M'$ is a nonzero natural number with $q \nmid M'$, and $A$ is a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a non-unit of $A$. Write $k =$ `ResidueField A` for its residue field, $\mathcal F_{M'} =$ `modularFunctionFieldC k M'` for the intermediate field of `LaurentSeries k` generated over $k$ by the series `jqModC k` and `jqNModC k M'`, and $\mathcal F^{\mathrm{bar}}_{M'} =$ `modularFunctionFieldBar M'`, the base change `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M')` of the full level-$M'$ rational modular function field to $\overline{\mathbb Q}$. Further, $\bar F =$ `fieldBar q M'` is `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, the base change to $\overline{\mathbb Q}$ of the rational function field of level $\Gamma_H(q^2M')$ with $H =$ `levelH q M'` the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, and $E =$ `xHFunctionFieldC k (q ^ 2 * M') (levelH q M')` is the corresponding field of $q$-expansion ratios of integral forms over $k$. Places are those of the project notion [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of the upper field containing the image of the base field, different from the whole field and with principal ideals; `ord`, `evalAt` and `IsRational` are the associated order function, residual evaluation and rationality of the residue field.
--
--   The data of the statement are: a finset $W$ of places of $\mathcal F_{M'}$ over $k$ together with the hypothesis `hW` that $W$ is exactly `ssPlaces q M' k`, i.e. the set of places $w$ which are rational, satisfy `IsAffineGeomPlace`, and whose value $w.\mathrm{evalAt}(\,$`jGeomGen k M'`$\,)$ lies in `ssJSet q k`; the inclusion `hle` of $\mathcal F^{\mathrm{bar}}_{M'}$ in $\bar F$; a constant reduction $R_0$ of type `ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC k M')`, that is, a valuation subring `R₀.integers` of $\mathcal F^{\mathrm{bar}}_{M'}$ with a surjective residue homomorphism onto $\mathcal F_{M'}$ whose kernel is the maximal ideal, inducing $x \in A$ on constants, together with the further clauses of that structure (compatibility with the residue of $A$ on constants, existence of a scaling with nonzero residue, and preservation of degrees and of divisors under its `placeMap`); the hypothesis `hR₀`, that for every Laurent series $y$ over $A$ whose coefficientwise image in `LaurentSeries (AlgebraicClosure ℚ)` lies in $\mathcal F^{\mathrm{bar}}_{M'}$, that element lies in `R₀.integers` and its $R_0$-residue, viewed as a Laurent series over $k$, is the coefficientwise reduction of $y$; an element $\pi \in \overline{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$; a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`); and two families of valuation subrings of $\bar F$, namely $O_{\mathrm{Ig}} : \mathbb P^1(\mathbb F_q) \to$ `ValuationSubring (fieldBar q M')` indexed by [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21), and $O_{\mathrm{ss}} : W \to$ `ValuationSubring (fieldBar q M')`.
--
--   The Igusa family is constrained by four hypotheses. `hIg_inf` describes the ring at the point `lineInfty q` $= [1:0]$: an element $f$ of $\bar F$ lies in $O_{\mathrm{Ig}}([1:0])$ if and only if there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot y = x$ after coefficientwise inclusion of $A$ into $\overline{\mathbb Q}$. `hIg` states that every $\ell$ is obtained from $[1:0]$ by some $\gamma \in \Gamma_0(M')$, in the sense that $\mathrm{red}_q(\gamma) \cdot [1:0] = \ell$ and $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}([1:0])$ along `levelAutBar q M' ζ γ`. `hIg_inj` states that $O_{\mathrm{Ig}}$ is injective. `hIg_perm` states that for every primitive $q$-th root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$ there is a permutation $\sigma$ of $\mathbb P^1(\mathbb F_q)$ with $O_{\mathrm{Ig}}(\ell)$ pulled back along `levelAutBar q M' ζ' γ` equal to $O_{\mathrm{Ig}}(\sigma \ell)$ for all $\ell$.
--
--   The supersingular family is constrained by three hypotheses. `hSS_A` says that for each $s$ a constant $x \in \overline{\mathbb Q}$ lies in $O_{\mathrm{ss}}(s)$ if and only if $x \in A$. `hSS_over` says, for $s \in W$ and $f \in$ `R₀.integers` subject to the cusp-regularity condition that $0 \le \operatorname{ord}_P(\hat\jmath)$ implies $0 \le \operatorname{ord}_P(f)$ for every place $P$ of $\mathcal F^{\mathrm{bar}}_{M'}$ over $\overline{\mathbb Q}$, where $\hat\jmath$ denotes the element `coeffEmb (AlgebraicClosure ℚ) jq` of $\mathcal F^{\mathrm{bar}}_{M'}$, and subject to the $R_0$-residue of $f$ lying in the valuation subring of $s$: first, the image of $f$ in $\bar F$ under `IntermediateField.inclusion hle` lies in $O_{\mathrm{ss}}(s)$, and second, for every $a \in A$ whose residue in $k$ equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of that image of $f$ and the constant $a$ lies in $O_{\mathrm{ss}}(s)$ and, as an element of that ring, lies in its maximal ideal. `hSS_fix` says that $O_{\mathrm{ss}}(s)$ is its own pullback along `levelAutBar q M' ζ' γ` for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$. `hSS_tr` says that for each $s \in W$ there is $t \in O_{\mathrm{ss}}(s)$ such that for every $a \in A$ the difference $t - a$ lies in $O_{\mathrm{ss}}(s)$ and is a unit there.
--
--   The descent data are: a subfield $K_0$ of $\overline{\mathbb Q}$ over which $\overline{\mathbb Q}$ is algebraic, with $\pi \in K_0$; a ring $A_0$ which is a Henselian local discrete valuation domain; an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ (`hιK₀`) and for which the composition of $\iota$ with the residue map of $A$ is surjective (`hres`); a generator $\varpi_0$ of the maximal ideal of $A_0$ (`hϖ₀`) whose image in $\overline{\mathbb Q}$ is $\pi$ (`hϖ₀π`); a subfield $F_0$ of $\bar F$ characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that the image of $\hat\jmath$ in $\bar F$ lies in $F_0$; and an $A_0$-algebra structure on $F_0$ whose structure map is, by `hj₀`, given by $\iota$ followed by the constants embedding $\overline{\mathbb Q} \to \bar F$. The element $\hat\jmath$ of $F_0$ is nonzero, so that the chart algebra `TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ ⟨_, hjF₀⟩` is available: it is the subalgebra of elements of $F_0$ integral over the $A_0$-subalgebra generated by $\hat\jmath$.
--
--   Finally, fix $s \in W$ and $\ell \in \mathbb P^1(\mathbb F_q)$, put $O_\ell = O_{\mathrm{Ig}}(\ell) \cap F_0$ (the pullback of $O_{\mathrm{Ig}}(\ell)$ along the inclusion of $F_0$), and let $\rho$ be a ring homomorphism from the residue field of $O_\ell$ to $E$, and $\tau$ a ring endomorphism of `LaurentSeries k` which by `hτ` is either the identity or `qExpand k (q ^ 2)`, the substitution $Q \mapsto Q^{q^2}$. The compatibility hypotheses on $\rho$ are: `hρA`, that for $a \in A_0$ whose image $\mathrm{algebraMap}\,a$ lies in $O_\ell$, $\rho$ of its residue class is the constant of $E$ given by the residue of $\iota a$ in $k$; and `hρf`, that for $f \in$ `R₀.integers`, $a \in A_0$ and $g$ in the chart algebra with $g \in O_\ell$, if the image of $g$ in $\bar F$ equals the image of $f$ minus the constant $\iota a$, then the Laurent series underlying $\rho$ of the residue class of $g$ equals $\tau$ applied to the Laurent series of the $R_0$-residue of $f$, minus the constant Laurent series of the residue of $\iota a$ in $k$. Let $w$ be a place of $E$ over $k$ subject to two hypotheses: `hwC`, that $\rho$ of the residue class of $g$ lies in the valuation subring of $w$ for every chart element $g$ lying in $O_\ell$; and `hread`, that for every $f \in$ `R₀.integers` satisfying the above cusp-regularity condition relative to $\hat\jmath$ and whose $R_0$-residue lies in the valuation subring of $s$, for every $a \in A_0$ with residue of $\iota a$ equal to $s.\mathrm{evalAt}$ of that $R_0$-residue, and for every chart element $g$ lying in $O_\ell$ whose image in $\bar F$ is the image of $f$ minus the constant $\iota a$, the element $\rho$ of the residue class of $g$ lies in the non-units of the valuation subring of $w$.
--
--   Conclusion: for every $g \in \mathcal F_{M'}$ and every $g' \in E$ such that the Laurent series of $g'$ is $\tau$ of the Laurent series of $g$, one has $g$ in the valuation subring of $s$ if and only if $g'$ is in the valuation subring of $w$.
--
--   This is the statement that the place $w$ of the reduced level-$\Gamma_H(q^2M')$ function field lies over the supersingular place $s$ of the reduced level-$M'$ field, the comparison being made through the Igusa chart at $\ell$ and the substitution $\tau$; it is the $q = 3$ case, the prime being fixed to $3$ in the hypotheses. It feeds the identification of places in [`ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_three`](thm.html#ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_three) on the Igusa-tower leg of the construction of the semistable covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three
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
    (ρ : IsLocalRing.ResidueField ↥((OIg ℓ).comap F₀.subtype) →+* ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (τ : LaurentSeries (ResidueField A) →+* LaurentSeries (ResidueField A)) (hτ : τ = RingHom.id _ ∨ τ = qExpand (ResidueField A) (q ^ 2))
    (hρA : ∀ (a : A₀) (ha : ((algebraMap A₀ ↥F₀ a : ↥F₀)) ∈ (OIg ℓ).comap F₀.subtype),
        ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨algebraMap A₀ ↥F₀ a, ha⟩) =
          algebraMap (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) (IsLocalRing.residue ↥A (ι a)))
    (hρf : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers) (a : A₀)
        (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype),
        ((g : ↥F₀) : ↥(fieldBar q M')) =
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
        ((ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩) : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
          τ ((R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A))
            - algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue ↥A (ι a)))
    (w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (hwC : ∀ (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype),
      ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩) ∈ w.toValuationSubring)
    (hread : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A₀, residue A (ι a) =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∀ (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype), ((g : ↥F₀) : ↥(fieldBar q M')) =
                (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
              ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩) ∈ w.toValuationSubring.nonunits)
    (g : ↥(modularFunctionFieldC (ResidueField A) M')) (g' : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (hgg' : (g' : LaurentSeries (ResidueField A)) = τ (g : LaurentSeries (ResidueField A))) :
    g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ g' ∈ w.toValuationSubring := by sorry
