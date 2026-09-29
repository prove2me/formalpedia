-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent_of_eq_two
-- name    : ModularCurve.FullLevel.formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/f1ceb5d3-af92-5296-b58b-b1470a64f8f9
-- title:
--   Formal smoothness of the descended Igusa ring at q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a non-zero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places, i.e. the rational affine geometric places at which $\mathrm{jGeomGen}$ evaluates into $\mathrm{ssJSet}\,q$. Assume the base-changed full-level field $\mathrm{modularFunctionFieldBar}\,M'$ sits inside $\mathrm{fieldBar}\,q\,M'$ (inclusion `hle`), and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$, compatible with coefficientwise reduction of Laurent series with coefficients in $A$ (`hR₀`). Let $\pi\in A$ satisfy $\pi^{q^2-1}=q$, let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb Q}$, and let $O_{\mathrm{Ig}}$, indexed by $\mathbb P^1(\mathbb Z/q)$, and $O_{\mathrm{SS}}$, indexed by $W$, be families of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ subject to: $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ consists of the $f$ for which there are Laurent series $x,y$ over $A$ with $y$ having non-zero reduction and $f\cdot y=x$; every line is of the form $\mathrm{redQ}\,q\,\gamma\cdot\mathrm{lineInfty}\,q$ for some $\gamma\in\Gamma_0(M')$ with $O_{\mathrm{Ig}}(\ell)$ the pullback of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; $O_{\mathrm{Ig}}$ is injective; and pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$, $\gamma\in\Gamma_0(M')$, permutes the family. For the supersingular rings it is assumed that $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ exactly in $A$; that any $f$ in the integers of $R_0$ which is regular wherever $j$ is and whose $R_0$-residue lies in the valuation ring of $s$ lands in $O_{\mathrm{SS}}(s)$, with $f-a$ in the maximal ideal of $O_{\mathrm{SS}}(s)$ whenever $a\in A$ reduces to $s.\mathrm{evalAt}$ of that residue; that each $O_{\mathrm{SS}}(s)$ is invariant under pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for $\gamma\in\Gamma_0(M')$; and that each $O_{\mathrm{SS}}(s)$ contains an element $t$ with $t-a$ a unit for all $a\in A$. Let $K_0$ be a subfield of $\overline{\mathbb Q}$ containing $\pi$ with $\overline{\mathbb Q}$ algebraic over it, and let $A_0$ be a henselian discrete valuation domain with an injective local ring homomorphism $\iota:A_0\to A$ whose image in $\overline{\mathbb Q}$ is $A\cap K_0$, such that reduction composed with $\iota$ is onto $\mathrm{ResidueField}\,A$, and with $\mathfrak m_{A_0}=(\varpi_0)$, $\iota(\varpi_0)=\pi$. Let $F_0$ be the subfield of $\mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$; it is assumed to contain the image of $j$ and to carry an $A_0$-algebra structure whose structure map is $a\mapsto\iota(a)$. Finally let $\ell\in\mathbb P^1(\mathbb Z/q)$ and let $S$ be an $A_0$-subalgebra of $F_0$ whose elements are exactly those lying in $O_{\mathrm{Ig}}(\ell)$. Then $S$ is formally smooth over $A_0$.
--
--   This is the formal smoothness of the Igusa chart of the component indexed by $\ell$ after descent to the field $F_0$ of Laurent expansions with coefficients in $K_0$ and to the henselian base $A_0$, in the case $q=2$ of the semistable covering of the full-level modular curve. It is used in the construction of Igusa-chart neighbourhoods with local rings localisations of this subalgebra and unique crossing behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent_of_eq_two.lean

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

theorem ModularCurve.FullLevel.formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent_of_eq_two
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
    (ℓ : CuspidalType.ProjLine q)

    (S : Subalgebra A₀ ↥F₀) (hS : ∀ f : ↥F₀, f ∈ S ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ) :
    Algebra.FormallySmooth A₀ ↥S := by sorry
