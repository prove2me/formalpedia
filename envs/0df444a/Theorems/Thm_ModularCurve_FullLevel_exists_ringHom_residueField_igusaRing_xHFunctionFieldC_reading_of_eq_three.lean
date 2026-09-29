-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_three
-- name    : ModularCurve.FullLevel.exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/3d393022-56e0-5858-9eac-7da801ad491a
-- title:
--   Igusa component residue field embeds into reduced level-H field, q=3
-- statement:
--   Let $q$ be a prime equal to $3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of the function field $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ consisting exactly of the supersingular places (rational, affine geometric, with $\mathrm{jGeomGen}$ evaluating into the supersingular $j$-set), assume the base-changed full level-$M'$ field $\mathrm{modularFunctionFieldBar}\,M'$ sits inside $\mathrm{fieldBar}\,q\,M'$, the $\overline{\mathbb Q}$-base change of the level-$H$ field at level $q^2M'$ for $H=\mathrm{levelH}\,q\,M'$ the kernel of $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, i.e. the units $\equiv 1 \bmod q$. Let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to the level-$M'$ field over $\mathrm{ResidueField}\,A$ (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map with kernel the maximal ideal, compatible with constants, together with a degree- and divisor-compatible map on places), and assume $R_0$ computes coefficientwise reductions: every Laurent series $y$ over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$ with residue the coefficientwise reduction of $y$. Let $\pi \in \overline{\mathbb Q}$ satisfy $\pi^{q^2-1}=q$ and $\pi \in A$, let $\zeta$ be a primitive $q$-th root of unity, and let $O_{\mathrm{Ig}} : \mathbb P^1(\mathbb Z/q) \to$ valuation subrings of $\mathrm{fieldBar}\,q\,M'$ and $O_{\mathrm{SS}} : W \to$ valuation subrings satisfy: $O_{\mathrm{Ig}}(\infty)$ is the Gauss-type ring of $f$ with $f\cdot y = x$ for Laurent series $x,y$ over $A$ with $y$ of nonzero reduction; each $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\infty)$ along some $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma \in \Gamma_0(M')$ moving $\infty$ to $\ell$; $O_{\mathrm{Ig}}$ is injective and is permuted by all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$, $\gamma \in \Gamma_0(M')$; each $O_{\mathrm{SS}}(s)$ meets the constants exactly in $A$, is invariant under those same automorphisms, contains an element $t$ with $t-a$ a unit for all $a \in A$, and receives every $f \in R_0.\mathrm{integers}$ which is regular wherever $\hat\jmath$ is and whose $R_0$-residue lies in the valuation ring of $s$, with $f-a$ in the maximal ideal of $O_{\mathrm{SS}}(s)$ whenever the residue of $a \in A$ is the value at $s$ of that $R_0$-residue. Finally let $K_0 \subseteq \overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$, let $A_0$ be a henselian discrete valuation domain with an injective local homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is $A \cap K_0$, inducing a surjection onto $\mathrm{ResidueField}\,A$ and sending a generator $\varpi_0$ of the maximal ideal to $\pi$; let $F_0$ be the subfield of $\mathrm{fieldBar}\,q\,M'$ of series all of whose coefficients lie in $K_0$, containing the image $\hat\jmath$ of $j_q$, with $A_0$-algebra structure given by $\iota$ followed by the constant embedding, and $\hat\jmath \neq 0$. Then for every $\ell \in \mathbb P^1(\mathbb Z/q)$ there is a ring homomorphism $\rho$ from the residue field of the valuation subring $O_\ell := O_{\mathrm{Ig}}(\ell) \cap F_0$ of $F_0$ to the level-$H$ $q$-expansion field $\mathrm{xHFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,(q^2M')\,(\mathrm{levelH}\,q\,M')$ such that the latter is algebraic over the image of $\rho$, together with a ring endomorphism $\tau$ of $\mathrm{LaurentSeries}\,(\mathrm{ResidueField}\,A)$ which is either the identity or $\mathrm{qExpand}$ with parameter $q^2$, with the properties: $\rho$ carries the residue of the image of any $a \in A_0$ lying in $O_\ell$ to the constant given by the residue of $\iota a$; and for all $f \in R_0.\mathrm{integers}$, $a \in A_0$ and $g$ in the chart algebra $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$ of elements of $F_0$ integral over $A_0[\hat\jmath]$ with $g \in O_\ell$ and $g = f - \iota a$ in $\mathrm{fieldBar}\,q\,M'$, the Laurent series of $\rho$ of the residue of $g$ equals $\tau$ applied to the Laurent series of the $R_0$-residue of $f$, minus the constant series attached to the residue of $\iota a$.
--
--   This is the Igusa-chart step in the construction of a semistable model of the modular curve at $q$: it identifies the residue field of an Igusa component of the descended two-chart model, over the henselian base $A_0$ inside $K_0$, with a subfield of the level-$H$ function field in characteristic $q$ over which that field is algebraic, and records how $A$-integral level-$M'$ functions are read there, either directly or after the substitution $q \mapsto q^{q^2}$. It is the case $q = 3$, where the Igusa covering of the branch at infinity is trivial, and it feeds the statements on rational places of the chart algebra and on the uniqueness of the Igusa valuation subring in the descended model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_three
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
