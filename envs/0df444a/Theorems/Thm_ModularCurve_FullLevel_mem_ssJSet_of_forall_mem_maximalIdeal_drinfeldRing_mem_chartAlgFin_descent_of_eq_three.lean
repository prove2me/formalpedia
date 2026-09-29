-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_three
-- name    : ModularCurve.FullLevel.mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/0c5647a8-be6e-52ed-ab20-27eac17cd2c4
-- title:
--   Supersingular j-value at a Drinfeld point, q = 3
-- statement:
--   Fix a prime $q$ with $q = 3$ and a level $M' \neq 0$ with $q \nmid M'$, and a valuation subring $A \subseteq \overline{\mathbb Q}$ in which $q$ is a non-unit. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places, i.e. those $w$ that are rational, affine geometric, and satisfy $w(\,j_{\mathrm{geom}}\,) \in \mathrm{ssJSet}\,q$. Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to that residual function field (a valuation subring with surjective residue map of kernel the maximal ideal, compatible with $A$ and with orders of places), satisfying the coefficientwise compatibility $hR_0$: every Laurent series with coefficients in $A$ lying in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral with residue the coefficientwise reduction. Further data: $\pi \in A$ with $\pi^{q^2-1} = q$; a primitive $q$-th root of unity $\zeta$; families $\mathcal O_{\mathrm{Ig}}$ indexed by $\mathbb P^1(\mathbb F_q)$ and $\mathcal O_{\mathrm{ss}}$ indexed by $W$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$, subject to: $\mathcal O_{\mathrm{Ig}}(\infty)$ consists of the ratios $x/y$ of Laurent series over $A$ with $y$ of non-zero reduction; each $\mathcal O_{\mathrm{Ig}}(\ell)$ is the pullback of $\mathcal O_{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma \in \Gamma_0(M')$ carrying $\infty$ to $\ell$; $\mathcal O_{\mathrm{Ig}}$ injective and permuted by all such pullbacks; each $\mathcal O_{\mathrm{ss}}(s)$ meets $\overline{\mathbb Q}$ in exactly $A$, is invariant under these pullbacks, contains an element $t$ with $t - a$ a unit for all $a \in A$, and lies over $s$ in the sense that an $R_0$-integral $f$ whose order is non-negative wherever that of $j$ is and whose $R_0$-residue is $s$-integral maps into $\mathcal O_{\mathrm{ss}}(s)$, with $f - a$ in the maximal ideal whenever the residue of $a \in A$ is the value of that residue at $s$. Finally, let $K_0 \subseteq \overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}/K_0$ algebraic and $\pi \in K_0$; let $A_0$ be a henselian discrete valuation domain with an injective local homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is $A \cap K_0$ and which induces a surjection onto $\mathrm{ResidueField}\,A$, with uniformiser $\varpi_0$ satisfying $\iota(\varpi_0) = \pi$; let $F_0 \subseteq \mathrm{fieldBar}\,q\,M'$ be the subfield of elements all of whose Laurent coefficients lie in $K_0$, an $A_0$-algebra via $\iota$, and assume the image $\hat\jmath$ of $j$ lies in $F_0$ and is non-zero. Let $\mathfrak n$ be a maximal ideal of $\mathrm{TwoChartIntegralModel.chartAlgFin}\,A_0\,F_0\,\hat\jmath$ (the $A_0$-subalgebra of elements of $F_0$ integral over $A_0[\hat\jmath]$) containing $\varpi_0$, and suppose there is $s \in W$ such that every element of this subalgebra whose image lies in the maximal ideal of $\mathcal O_{\mathrm{ss}}(s)$ lies in $\mathfrak n$. Then for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from that subalgebra to $\Omega$ with kernel $\mathfrak n$, the element $\varphi(\mathrm{jChartFin}\,A_0\,F_0\,\hat\jmath)$ lies in $\mathrm{ssJSet}\,q\,\Omega$: every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no non-zero point killed by $q$.
--
--   This is the converse implication in the Drinfeld/Igusa dichotomy for the descended two-chart integral model: a closed special point of the model lying in the maximal ideal of a Drinfeld valuation ring attached to a supersingular place has supersingular $j$-invariant. It is the $q = 3$ case, proved from the corresponding statement producing an element of $A$ with $j$-invariant congruent to the value of the point, together with transport of supersingularity along ring homomorphisms of algebraically closed fields of characteristic $q$, and it feeds the subsequent dichotomy between formally smooth centred subalgebras and points lying over the Gauss ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_three
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
    (𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫 : 𝔫.IsMaximal)
    (hϖ : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫)
    (s : ↥W)
    (hs : ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) → g ∈ 𝔫)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* Ω) (hφ : RingHom.ker φ = 𝔫) :
    φ (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ∈ ModularCurve.ssJSet q Ω := by sorry
