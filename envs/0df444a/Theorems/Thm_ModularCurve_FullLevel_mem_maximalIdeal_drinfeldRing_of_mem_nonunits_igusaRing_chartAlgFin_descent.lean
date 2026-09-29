-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent
-- name    : ModularCurve.FullLevel.mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/6f7d5663-a1e4-58e3-ae2b-c18f6f885620
-- title:
--   Igusa non-units of the descended chart are Drinfeld-central
-- statement:
--   Let $q\ge 5$ be a prime, let $M'\ne 0$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit, with residue field $\kappa_A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa_A\,M'$ over $\kappa_A$ whose members are exactly the supersingular places (rational, affine-geometric places at which the geometric $j$-generator takes a supersingular value); assume $\mathrm{modularFunctionFieldBar}\,M'\le\overline F:=\mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}\,\kappa_A\,M'$ whose residue map computes coefficientwise reduction on Laurent series with coefficients in $A$. Let $\pi\in A$ satisfy $\pi^{q^2-1}=q$, let $\zeta$ be an index of primitive $q$-th roots of unity, and let $O_{\mathrm{Ig}}$ and $O_{\mathrm{ss}}$ be families of valuation subrings of $\overline F$ indexed by $\mathbb P^1(\mathbb Z/q)$ and by $W$, subject to: $O_{\mathrm{Ig}}(\infty)$ consists of the quotients $x/y$ of Laurent series with coefficients in $A$ with $y$ having nonzero coefficientwise reduction; each $\ell$ is $\mathrm{redQ}\,q\,\gamma\cdot\infty$ for some $\gamma\in\Gamma_0(M')$ with $O_{\mathrm{Ig}}(\ell)$ the pullback of $O_{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; $O_{\mathrm{Ig}}$ injective; pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ ($\gamma\in\Gamma_0(M')$) permutes the $O_{\mathrm{Ig}}(\ell)$; each $O_{\mathrm{ss}}(s)$ meets $\overline{\mathbb Q}$ exactly in $A$, is invariant under all these pullbacks, and contains an element $t$ with $t-a$ a unit for every $a\in A$; and, for $f$ in $R_0$'s valuation ring which is regular at every place where $\hat\jmath$ is and whose $R_0$-residue lies in the valuation ring of $s$, the image of $f$ lies in $O_{\mathrm{ss}}(s)$ and $f-a$ lies in the maximal ideal whenever $a\in A$ reduces to the value of that residue at $s$. Let further $K_0$ be a subfield of $\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$, let $A_0$ be a henselian discrete valuation domain with an injective local ring homomorphism $\iota:A_0\to A$ whose image in $\overline{\mathbb Q}$ is $A\cap K_0$, with $A_0\to\kappa_A$ surjective and a uniformiser $\varpi_0$ with $\iota\varpi_0=\pi$, and let $F_0\subseteq\overline F$ be the subfield of elements all of whose Laurent coefficients lie in $K_0$, containing the nonzero element $\hat\jmath$ (the base change of the $j$-expansion), with the $A_0$-algebra structure on $F_0$ induced by $\iota$. Then for every $s\in W$, every $\ell\in\mathbb P^1(\mathbb Z/q)$ and every $g\in F_0$ integral over $A_0[\hat\jmath]$ whose image in $\overline F$ is a non-unit of $O_{\mathrm{Ig}}(\ell)$, that image lies in $O_{\mathrm{ss}}(s)$ and belongs to the maximal ideal of $O_{\mathrm{ss}}(s)$.
--
--   This is the statement that every Igusa component of the descended two-chart model passes through the contracted Drinfeld (supersingular) point attached to each $s\in W$, in the form: on the finite chart algebra, being a non-unit at an Igusa ring forces membership in the Drinfeld maximal ideal. It feeds the refinement asserting a unique such maximal ideal over each supersingular place in the semistable model of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent.lean

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

theorem ModularCurve.FullLevel.mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent
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
    (s : ↥W) (ℓ : CuspidalType.ProjLine q)
    (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits) :
    ∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s) := by sorry
