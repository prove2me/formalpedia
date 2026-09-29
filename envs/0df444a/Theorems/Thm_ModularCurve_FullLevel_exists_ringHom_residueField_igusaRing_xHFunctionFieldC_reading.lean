-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading
-- name    : ModularCurve.FullLevel.exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/80fee0ab-0387-527e-b803-7610a0ac565a
-- title:
--   Igusa component residue field reads in the reduced level-H field
-- statement:
--   Fix a prime $q\ge 5$ and $M'\neq 0$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places (rational, affine-geometric, with $j$-value in the supersingular set). Assume the base change $\mathrm{modularFunctionFieldBar}\,M'$ of the full level-$M'$ function field to $\overline{\mathbb Q}$ is contained in $\mathrm{fieldBar}\,q\,M'$, the base change of the function field of level $\Gamma_H(q^2M')$ for $H=\ker\big((\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times\big)$. Let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to the reduced level-$M'$ field (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map with kernel the maximal ideal, compatible with $A$, together with a degree- and divisor-compatible place map), satisfying the Gauss condition $hR_0$: every Laurent series $y$ with coefficients in $A$ whose image lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$ and has residue the coefficientwise reduction of $y$. Fix $\pi\in A$ with $\pi^{q^2-1}=q$, an index $\zeta$ given by a primitive $q$-th root of unity, families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb Z/q)$ and $O_{\mathrm{ss}}$ indexed by $W$, subject to: $O_{\mathrm{Ig}}(\infty)$ consists of the $f$ admitting Laurent series $x,y$ over $A$ with $y$ of non-zero reduction and $f\cdot y=x$; each $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma\in\Gamma_0(M')$ with $\bar\gamma\cdot\infty=\ell$; $O_{\mathrm{Ig}}$ is injective and its family is permuted by all pullbacks along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$, $\gamma\in\Gamma_0(M')$; each $O_{\mathrm{ss}}(s)$ meets $\overline{\mathbb Q}$ exactly in $A$, is invariant under all those pullbacks, contains an element $t$ with $t-a$ a unit for all $a\in A$, and satisfies the specialisation condition $hSS\_over$: for $f\in R_0.\mathrm{integers}$ of non-negative order at every place where the image of $jq$ has non-negative order and with $R_0$-residue in the valuation ring of $s$, the image of $f$ lies in $O_{\mathrm{ss}}(s)$, and $f-a$ lies in the maximal ideal of $O_{\mathrm{ss}}(s)$ whenever $a\in A$ reduces to the value of the residue of $f$ at $s$. Finally let $K_0\subseteq\overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}$ algebraic over it and $\pi\in K_0$, let $A_0$ be a henselian discrete valuation domain with an injective local ring map $\iota:A_0\to A$ whose image in $\overline{\mathbb Q}$ is $A\cap K_0$, with $\mathrm{residue}\circ\iota$ surjective and a uniformiser $\varpi_0$ generating the maximal ideal with $\iota\varpi_0=\pi$; let $F_0$ be the subfield of $\mathrm{fieldBar}\,q\,M'$ of elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of $jq$, and equipped with an $A_0$-algebra structure induced by $\iota$, with $\hat\jmath\neq0$. Then for every $\ell\in\mathbb P^1(\mathbb Z/q)$ there is a ring homomorphism $\rho$ from the residue field of $O_{\mathrm{Ig}}(\ell)\cap F_0$ to $\mathrm{xHFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,(q^2M')\,H$ whose target is algebraic over its range, together with $\tau$ on $\mathrm{LaurentSeries}\,(\mathrm{ResidueField}\,A)$ equal either to the identity or to $\mathrm{qExpand}$ of index $q^2$, such that $\rho$ carries the residue class of $\mathrm{algebraMap}\,a$, for $a\in A_0$ with that image in $O_{\mathrm{Ig}}(\ell)\cap F_0$, to the image of the residue of $\iota a$, and such that for all $f\in R_0.\mathrm{integers}$, $a\in A_0$ and $g$ in $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$ lying in $O_{\mathrm{Ig}}(\ell)\cap F_0$ with $g=f-\iota a$ in $\mathrm{fieldBar}\,q\,M'$, the Laurent series of $\rho$ of the residue class of $g$ equals $\tau$ applied to the Laurent series of the $R_0$-residue of $f$ minus the constant series given by the residue of $\iota a$.
--
--   This is the reading of the residue field of an Igusa component of the descended two-chart model inside the reduced level-$H$ $q$-expansion function field over the residue field of $A$, in the style of the component structure of Igusa curves; the dichotomy for $\tau$ reflects that a level automorphism carrying $\ell$ to $\infty$ acts on level-$M'$ elements either by $q\mapsto q^{q^2}$ or by a twist by a $q$-th root of unity, which reduces to the identity in characteristic $q$. It is used by [`ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent`](thm.html#ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent) and by [`ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent`](thm.html#ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading.lean

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

open AlgebraicCurve IsLocalRing CongruenceSubgroup
open ModularCurve
open ModularCurve.FullLevel
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading
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
    (ℓ : CuspidalType.ProjLine q)
    :
    ∃ ρ : IsLocalRing.ResidueField ↥((OIg ℓ).comap F₀.subtype) →+* ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
    Algebra.IsAlgebraic ↥ρ.fieldRange ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) ∧
    ∃ τ : LaurentSeries (ResidueField A) →+* LaurentSeries (ResidueField A), (τ = RingHom.id _ ∨ τ = qExpand (ResidueField A) (q ^ 2)) ∧
      (∀ (a : A₀) (ha : ((algebraMap A₀ ↥F₀ a : ↥F₀)) ∈ (OIg ℓ).comap F₀.subtype),
        ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨algebraMap A₀ ↥F₀ a, ha⟩) =
          algebraMap (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) (IsLocalRing.residue ↥A (ι a))) ∧
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers) (a : A₀)
        (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype),
        ((g : ↥F₀) : ↥(fieldBar q M')) =
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
        ((ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩) : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
          τ ((R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A))
            - algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue ↥A (ι a))) := by sorry
