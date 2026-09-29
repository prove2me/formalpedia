-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_of_isMaximal_of_mem_nonunits_igusaRing_of_floorTrace_chartAlgFin_descent_of_eq_three
-- name    : ModularCurve.FullLevel.eq_of_isMaximal_of_mem_nonunits_igusaRing_of_floorTrace_chartAlgFin_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/521b0d26-d697-5146-ad77-a1d471693856
-- title:
--   Uniqueness of the closed point over a floor place, q=3
-- statement:
--   Throughout, $q$ is a prime with $q = 3$ (hypothesis `hq3`), $M'$ is a nonzero natural number with $q \nmid M'$ (`hqM'`), and $A$ is a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ belongs to the nonunits of $A$ (`hA`). The two function fields involved are $\overline{\mathbb Q}$-intermediate fields of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$: the field `modularFunctionFieldBar M'`, obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images of `modularFunctionFieldFull M'`, and `fieldBar q M'`, obtained likewise from `xHFunctionField (q^2*M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, that is the group of units congruent to $1$ modulo $q$. The hypothesis `hle` asserts the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`, and `IntermediateField.inclusion hle` denotes the resulting embedding.
--
--   A finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$ is given, with `hW` saying that $W$ consists exactly of the supersingular places, i.e. those places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}$ of the generator `jGeomGen` lying in `ssJSet q`. Further, $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'`: a valuation subring `R₀.integers` containing the image of $A$ exactly, a surjective residue homomorphism onto the reduced field with kernel the maximal ideal, a map on places compatible with degrees and with orders of functions, and the scaling property that every nonzero $f$ can be scaled into the integers with nonzero residue. The hypothesis `hR₀` states that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}$ lies in `modularFunctionFieldBar M'`, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$.
--
--   An element $\pi \in \overline{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$ is fixed (`hπ`, `hπP`), together with an index $\zeta$ in `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$; the automorphisms `levelAutBar q M' ζ' γ` of `fieldBar q M'` over $\overline{\mathbb Q}$ attached to $\zeta'$ and $\gamma \in SL(2,\mathbb Z)$ are used below. Two families of valuation subrings of `fieldBar q M'` are given: the Igusa family $O_{\mathrm{Ig}}$ indexed by [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) $= \mathbb P^1(\mathbb Z/q)$, and the family $O_{\mathrm{SS}}$ indexed by $W$.
--
--   The Igusa hypotheses are: `hIg_inf`, which describes $O_{\mathrm{Ig}}$ at the line `lineInfty q` as the set of $f$ for which there exist Laurent series $x, y$ over $A$ with nonzero coefficientwise reduction of $y$ and $f \cdot y = x$ after pushing coefficients into $\overline{\mathbb Q}$; `hIg`, which provides for each line $\ell$ some $\gamma \in \Gamma_0(M')$ with `redQ q γ` carrying `lineInfty q` to $\ell$ and $O_{\mathrm{Ig}}(\ell)$ equal to the preimage of $O_{\mathrm{Ig}}(\mathrm{lineInfty})$ under `levelAutBar q M' ζ γ`; `hIg_inj`, the injectivity of $\ell \mapsto O_{\mathrm{Ig}}(\ell)$; and `hIg_perm`, which for every index $\zeta'$ and every $\gamma \in \Gamma_0(M')$ yields a permutation $\sigma$ of $\mathbb P^1(\mathbb Z/q)$ such that the preimage of $O_{\mathrm{Ig}}(\ell)$ under `levelAutBar q M' ζ' γ` is $O_{\mathrm{Ig}}(\sigma \ell)$ for all $\ell$.
--
--   The supersingular hypotheses are: `hSS_A`, that for each $s$ and each $x \in \overline{\mathbb Q}$ the image of $x$ in `fieldBar q M'` lies in $O_{\mathrm{SS}}(s)$ precisely when $x \in A$; `hSS_over`, which for $s \in W$ and $f$ in `modularFunctionFieldBar M'` lying in `R₀.integers` assumes that $f$ has non-negative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the base-changed $j$-expansion `coeffEmb (AlgebraicClosure ℚ) jq` has non-negative order, and that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, and concludes that the image of $f$ in `fieldBar q M'` lies in $O_{\mathrm{SS}}(s)$ and that for every $a \in A$ whose residue equals the value at $s$ of the $R_0$-residue of $f$, the difference of the image of $f$ and the image of $a$ lies in $O_{\mathrm{SS}}(s)$ and in the maximal ideal of $O_{\mathrm{SS}}(s)$; `hSS_fix`, that $O_{\mathrm{SS}}(s)$ is its own preimage under every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; and `hSS_tr`, that for each $s$ there is $t \in O_{\mathrm{SS}}(s)$ such that for every $a \in A$ the difference $t - a$ lies in $O_{\mathrm{SS}}(s)$ and is a unit there.
--
--   The descent data are: a subfield $K_0 \subseteq \overline{\mathbb Q}$ over which $\overline{\mathbb Q}$ is algebraic, with $\pi \in K_0$ (`hπK₀`); a discrete valuation ring $A_0$ which is a henselian local domain, together with an injective local ring homomorphism $\iota : A_0 \to A$ (`hι`) whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ as a set (`hιK₀`) and for which the composite of $\iota$ with the residue map of $A$ is surjective (`hres`); a uniformiser $\varpi_0$ generating the maximal ideal of $A_0$ (`hϖ₀`) whose image in $\overline{\mathbb Q}$ is $\pi$ (`hϖ₀π`); a subfield $F_0$ of `fieldBar q M'` characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that the image under `IntermediateField.inclusion hle` of the base-changed $j$-expansion lies in $F_0$; and an $A_0$-algebra structure on $F_0$ compatible with $\iota$ in the sense of `hj₀`, namely that `algebraMap A₀ F₀ a` is the image in `fieldBar q M'` of $\iota a \in A \subseteq \overline{\mathbb Q}$, the distinguished element $\hat\jmath := \langle$ the image of the $j$-expansion, `hjF₀` $\rangle$ of $F_0$ being nonzero.
--
--   Finally, a place $s \in W$ and a line $\ell \in \mathbb P^1(\mathbb Z/q)$ are fixed, and $\mathfrak n, \mathfrak n'$ are maximal ideals (`h𝔫`, `h𝔫'`) of the $A_0$-subalgebra `TwoChartIntegralModel.chartAlgFin A₀ F₀ ĵ` of $F_0$, which consists of the elements of $F_0$ integral over $A_0[\hat\jmath]$. The hypotheses `hℓ` and `hℓ'` state that every $g$ in this subalgebra whose image in `fieldBar q M'` is a nonunit of $O_{\mathrm{Ig}}(\ell)$ lies in $\mathfrak n$, respectively in $\mathfrak n'$. The hypotheses `htr` and `htr'` state the floor-trace condition at $s$: for every $f$ in `modularFunctionFieldBar M'` lying in `R₀.integers`, subject to the same two conditions as in `hSS_over` (non-negative order wherever the base-changed $j$-expansion has non-negative order, and $R_0$-residue in the valuation subring of $s$), and for every $a \in A_0$ with $\mathrm{residue}_A(\iota a)$ equal to the value at $s$ of the $R_0$-residue of $f$, every $g$ in the subalgebra whose image in `fieldBar q M'` equals the image of $f$ minus the image of $\iota a$ lies in $\mathfrak n$, respectively in $\mathfrak n'$.
--
--   Under all of these hypotheses the conclusion is the single equality $\mathfrak n = \mathfrak n'$.
--
--   This is the uniqueness half of the statement that, on a fixed Igusa component of the descended two-chart integral model, there is exactly one closed point whose floor trace is a given supersingular place; the $q = 3$ case, with the hypothesis $q = 3$ in place of the lower bound used for the remaining primes. It is used in the proof of [`ModularCurve.FullLevel.exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_unique_chartAlgFin_descent_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_unique_chartAlgFin_descent_of_eq_three), which combines it with the corresponding existence statement, and it relies on the comparison of valuation subrings of the reduced field over the Igusa ring, on the localisation description of the finite chart, and on the unit property of $\hat\jmath - a$ coming from the Gauss-type argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_of_isMaximal_of_mem_nonunits_igusaRing_of_floorTrace_chartAlgFin_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.eq_of_isMaximal_of_mem_nonunits_igusaRing_of_floorTrace_chartAlgFin_descent_of_eq_three
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
    (𝔫 𝔫' : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫 : 𝔫.IsMaximal) (h𝔫' : 𝔫'.IsMaximal)
    (hℓ : ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits → g ∈ 𝔫)
    (hℓ' : ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits → g ∈ 𝔫')
    (htr : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
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
              g ∈ 𝔫))
    (htr' : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
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
              g ∈ 𝔫')) :
    𝔫 = 𝔫' := by sorry
