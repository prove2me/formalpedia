-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_two
-- name    : ModularCurve.FullLevel.exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/a90c21b7-88a8-5c70-a83c-e5adcd21faee
-- title:
--   Residue field of an Igusa component embeds, q=2
-- statement:
--   Fix the prime $q$ with $q = 2$, a level $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$. Assume: $W$ is the finset of places of $\mathrm{modularFunctionFieldC}(\kappa_A, M')$ over $\kappa_A = \mathrm{ResidueField}\,A$ whose members are exactly the supersingular ones (rational, affine geometric, with value of the geometric $j$ in the supersingular set); $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ via `hle`; $R_0$ is a `ConstantReduction` of $A$ from the geometric full level-$M'$ field to $\mathrm{modularFunctionFieldC}(\kappa_A,M')$ whose residue computes coefficientwise reduction of Laurent series with coefficients in $A$; $\pi \in A$ satisfies $\pi^{q^2-1} = q$; $\zeta$ is a primitive $q$-th root of unity; $O_{\mathrm{Ig}}$ assigns a valuation subring of $\mathrm{fieldBar}\,q\,M'$ to each point of $\mathbb P^1(\mathbb Z/q)$ and $O_{\mathrm{SS}}$ one to each $s \in W$, subject to: $O_{\mathrm{Ig}}(\infty)$ consists of the $f$ with $f\cdot y = x$ for Laurent series $x,y$ over $A$ with $y$ of nonzero reduction; each $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma \in \Gamma_0(M')$ carrying $\infty$ to $\ell$; $O_{\mathrm{Ig}}$ injective and its family permuted by all such pullbacks; $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ in $A$, is fixed by all those pullbacks, contains an element $t$ with $t - a$ a unit for all $a \in A$, and receives the $R_0$-integral floor elements regular where $j$ is, with $f - a$ in the maximal ideal when $\mathrm{res}_A(a)$ is the value of $s$ at the reduction of $f$. Assume further a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$, a henselian discrete valuation domain $A_0$ with an injective local homomorphism $\iota : A_0 \to A$ whose image is $A \cap K_0$, with $\mathrm{res}_A \circ \iota$ surjective and a uniformiser $\varpi_0$ with $\iota\varpi_0 = \pi$; $F_0$ the subfield of $\mathrm{fieldBar}\,q\,M'$ of elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of $jq$ and nonzero there, with $A_0$-algebra structure induced by $\iota$. Then for every $\ell \in \mathbb P^1(\mathbb Z/q)$ there is a ring homomorphism $\rho$ from the residue field of $O_{\mathrm{Ig}}(\ell) \cap F_0$ into $\mathrm{xHFunctionFieldC}(\kappa_A, q^2M', \mathrm{levelH}\,q\,M')$ such that the latter is algebraic over the range of $\rho$, and there is $\tau : \kappa_A(\!(q)\!) \to \kappa_A(\!(q)\!)$ equal either to the identity or to $\mathrm{qExpand}\,\kappa_A\,(q^2)$, for which: $\rho$ sends the residue class of $\mathrm{algebraMap}\,a$, for $a \in A_0$ lying in $O_{\mathrm{Ig}}(\ell) \cap F_0$, to the image of $\mathrm{res}_A(\iota a)$; and whenever $f$ is in $R_0.\mathrm{integers}$, $a \in A_0$, and $g$ lies in $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$ and in $O_{\mathrm{Ig}}(\ell)\cap F_0$ with $g = f - \iota a$ in $\mathrm{fieldBar}\,q\,M'$, then the Laurent series of $\rho$ of the residue class of $g$ equals $\tau$ of the Laurent series of $R_0$'s residue of $f$ minus the constant $\mathrm{res}_A(\iota a)$.
--
--   This is the Igusa-component case of the comparison between the residue fields of the descended two-chart integral model of $X_H(q^2M')$ and the reduced level-$H$ $q$-expansion function field in characteristic $q$, the reading of floor elements being either direct or through the substitution $q \mapsto q^{q^2}$. It is the twin, for $q = 2$, of the corresponding statement for $q \ge 5$, and is used in the identification of the valuation subrings attached to Igusa components and in the production of rational places on the chart algebra of the descended model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_two
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
