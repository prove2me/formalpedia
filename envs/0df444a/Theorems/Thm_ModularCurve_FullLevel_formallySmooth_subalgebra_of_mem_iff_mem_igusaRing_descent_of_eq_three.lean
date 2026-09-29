-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent_of_eq_three
-- name    : ModularCurve.FullLevel.formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/6497320d-3635-5b5d-88c9-b747abc7f3fd
-- title:
--   Formal smoothness of the descended Igusa ring, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'\neq 0$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a nonunit (`A.LiesOverPrime q`), with residue field $\kappa_A$. Let $W$ be a finite set of places of the characteristic-$\kappa_A$ modular function field `modularFunctionFieldC κ_A M'` (valuation subrings containing the base field, proper, with principal ideals) whose members are exactly the supersingular places: rational, affine geometric, and with $j$-value in the supersingular set. Assume `modularFunctionFieldBar M' ≤ fieldBar q M'`, where the first is the base change to $\overline{\mathbb Q}$ of the full level-$M'$ modular function field inside Laurent series, the second the base change of the function field of level $q^2M'$ with $H=\ker\big((\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times\big)$. Let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` along $A$ with values in `modularFunctionFieldC κ_A M'`, compatible with coefficientwise reduction of Laurent series over $A$ (hypothesis `hR₀`). Let $\pi\in A$ satisfy $\pi^{q^2-1}=q$, let $\zeta$ be a primitive $q$-th root of unity, and let $\mathcal O_{\mathrm{Ig}}$ and $\mathcal O_{\mathrm{SS}}$ be families of valuation subrings of `fieldBar q M'` indexed by $\mathbb P^1(\mathbb Z/q)$ and by $W$. The Igusa family is assumed to satisfy: $\mathcal O_{\mathrm{Ig}}$ at the line $[1:0]$ consists of those $f$ for which there are Laurent series $x,y$ over $A$ with $y$ having nonzero coefficientwise reduction and $f\cdot y=x$; every line is $\overline{\gamma}\cdot[1:0]$ for some $\gamma\in\Gamma_0(M')$ with the corresponding ring the pullback of the one at $[1:0]$ along `levelAutBar q M' ζ γ`; $\mathcal O_{\mathrm{Ig}}$ is injective; and pullback along `levelAutBar q M' ζ' γ` permutes the family, for all $\zeta'$ and $\gamma\in\Gamma_0(M')$. The supersingular family is assumed to satisfy: constants of $\overline{\mathbb Q}$ lie in $\mathcal O_{\mathrm{SS}}(s)$ exactly when they lie in $A$; for $f$ in the integers of $R_0$ with non-negative order at every place where $j$ has non-negative order and with $R_0$-residue in the valuation subring of $s$, the image of $f$ lies in $\mathcal O_{\mathrm{SS}}(s)$, and for every $a\in A$ whose residue is the value of the $R_0$-residue of $f$ at $s$ the difference $f-a$ lies in the maximal ideal of $\mathcal O_{\mathrm{SS}}(s)$; each $\mathcal O_{\mathrm{SS}}(s)$ is fixed by pullback along `levelAutBar q M' ζ' γ` for $\gamma\in\Gamma_0(M')$; and each $\mathcal O_{\mathrm{SS}}(s)$ contains an element $t$ with $t-a$ a unit for every $a\in A$. For the descent, let $K_0$ be a subfield of $\overline{\mathbb Q}$ over which $\overline{\mathbb Q}$ is algebraic, with $\pi\in K_0$; let $A_0$ be a henselian discrete valuation domain with an injective local ring homomorphism $\iota:A_0\to A$ whose image is $A\cap K_0$ and for which the composite with the residue map of $A$ is surjective, and let $\varpi_0$ generate the maximal ideal of $A_0$ with $\iota(\varpi_0)=\pi$. Let $F_0$ be the subfield of `fieldBar q M'` of elements all of whose Laurent coefficients lie in $K_0$, assume $j$ lies in $F_0$, and let the $A_0$-algebra structure on $F_0$ be the one induced by $\iota$ and the constants. Finally, let $\ell\in\mathbb P^1(\mathbb Z/q)$ and let $S$ be the $A_0$-subalgebra of $F_0$ whose elements are exactly those lying in $\mathcal O_{\mathrm{Ig}}(\ell)$. Then $S$ is formally smooth over $A_0$.
--
--   This is the local smoothness input on the Igusa leg of the semistable covering of the modular curve: the trace on the $K_0$-descended field $F_0$ of the Igusa valuation ring attached to a component $\ell$ is formally smooth over the henselian discrete valuation base $A_0$. It is the case $q=3$, and it feeds the construction of an Igusa chart whose local ring is a localisation of a formally smooth algebra with a unique crossing, used in [`ModularCurve.FullLevel.exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_igusaChart_localRing_eq_localization_formallySmooth_and_crossing_unique_of_normalModel_gen_j_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent_of_eq_three
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
    (ℓ : CuspidalType.ProjLine q)

    (S : Subalgebra A₀ ↥F₀) (hS : ∀ f : ↥F₀, f ∈ S ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ) :
    Algebra.FormallySmooth A₀ ↥S := by sorry
