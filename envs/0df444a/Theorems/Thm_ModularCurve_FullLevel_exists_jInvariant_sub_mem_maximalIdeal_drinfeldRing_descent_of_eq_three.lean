-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent_of_eq_three
-- name    : ModularCurve.FullLevel.exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/e785eb41-4469-53fb-b93a-a65f0554f009
-- title:
--   Drinfeld rings see jmatĥ as an A₀-constant: q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places, i.e. those that are rational, affine geometric and take the geometric $j$-value in the supersingular set $\mathrm{ssJSet}$. Assume the geometric full-level field $\mathrm{modularFunctionFieldBar}\,M'$ is contained in $\mathrm{fieldBar}\,q\,M' = \overline{\mathbb Q}\cdot F(\Gamma_H(q^2M'))$, and let $R_0$ be a constant reduction of $A$ from the former to $\mathrm{modularFunctionFieldC}$, compatible coefficientwise with reduction of Laurent series over $A$. Fix $\pi\in A$ with $\pi^{q^2-1}=q$, an index $\zeta$ of primitive $q$-th roots of unity, and families $\mathcal O_{\mathrm{Ig},\ell}$ ($\ell\in\mathbb P^1(\mathbb F_q)$) and $\mathcal O_{\mathrm{ss},s}$ ($s\in W$) of valuation subrings of $\mathrm{fieldBar}\,q\,M'$. The Igusa hypotheses, summarised here, describe $\mathcal O_{\mathrm{Ig},\infty}$ as the ring of quotients of Laurent series over $A$ with denominator of nonzero reduction, exhibit each $\mathcal O_{\mathrm{Ig},\ell}$ as the pullback of $\mathcal O_{\mathrm{Ig},\infty}$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma\in\Gamma_0(M')$ reducing to a matrix carrying $\mathrm{lineInfty}$ to $\ell$, assert injectivity of $\ell\mapsto\mathcal O_{\mathrm{Ig},\ell}$, and assert that pullback along any $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma\in\Gamma_0(M')$ permutes the family. The Drinfeld hypotheses, likewise summarised, say that an element of $\overline{\mathbb Q}$ lies in $\mathcal O_{\mathrm{ss},s}$ exactly when it lies in $A$; that any $f$ in the integers of $R_0$ whose order is nonnegative wherever that of the $q$-expansion $\hat\jmath$ of the modular invariant is, and whose $R_0$-residue lies in the valuation ring of $s$, maps into $\mathcal O_{\mathrm{ss},s}$ with $f-a$ in the maximal ideal for every $a\in A$ whose residue is the value of that residue at $s$; that each $\mathcal O_{\mathrm{ss},s}$ is fixed by pullback along all $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma\in\Gamma_0(M')$; and that each $\mathcal O_{\mathrm{ss},s}$ contains an element $t$ with $t-a$ a unit for all $a\in A$. Finally let $K_0\subseteq\overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}$ algebraic over it and $\pi\in K_0$; let $A_0$ be a henselian discrete valuation domain with an injective local ring homomorphism $\iota\colon A_0\to A$ whose image in $\overline{\mathbb Q}$ is $A\cap K_0$, with $\mathrm{residue}\circ\iota$ surjective onto the residue field of $A$, with $\mathfrak m(A_0)=(\varpi_0)$ and $\iota\varpi_0=\pi$; let $F_0$ be the subfield of $\mathrm{fieldBar}\,q\,M'$ of elements all of whose Laurent coefficients lie in $K_0$, assume $\hat\jmath\in F_0$, and let $F_0$ be an $A_0$-algebra whose structure map is induced by $\iota$. Then for every $s\in W$ there is $a\in A_0$ such that $\hat\jmath-a$, viewed in $\mathrm{fieldBar}\,q\,M'$, lies in $\mathcal O_{\mathrm{ss},s}$ and in its maximal ideal.
--
--   This is the descent step saying that each Drinfeld (supersingular) valuation ring of the geometric full-level field reduces the modular invariant to a constant coming from the henselian discrete valuation ring $A_0$; it is the $q=3$ case of a statement whose binders otherwise match those of the version assuming $q\ge 5$, the conclusion being the same. It feeds the subsequent analysis of the semistable covering, being used in the identification of Gauss rings, in the construction of maximal ideals of chart algebras and in the production of centred formally smooth subalgebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent_of_eq_three
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
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ)) :
    ∀ s : ↥W, ∃ (a : A₀) (h : (((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s),
      (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s) := by sorry
