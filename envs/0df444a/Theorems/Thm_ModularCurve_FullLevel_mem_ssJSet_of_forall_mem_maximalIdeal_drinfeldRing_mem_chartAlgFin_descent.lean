-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent
-- name    : ModularCurve.FullLevel.mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/6c1b05de-bc08-5c6d-bfdd-20d9e4f3916d
-- title:
--   Drinfeld centre at a supersingular place has supersingular j
-- statement:
--   Fix a prime $q \ge 5$ and a level $M' \neq 0$ with $q \nmid M'$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, and a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places (rational, affine-geometric places whose value at the generator $\mathrm{jGeomGen}$ is a supersingular $j$-invariant). Assume the geometric modular function field $\mathrm{modularFunctionFieldBar}\,M'$ sits inside $\mathrm{fieldBar}\,q\,M'$, and fix a constant reduction $R_0$ of the former to the residual function field, compatible coefficientwise with reduction of Laurent series over $A$; an element $\pi \in A$ with $\pi^{q^2-1} = q$; a primitive $q$-th root of unity index $\zeta$; families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to the Igusa hypotheses (the ring at $\infty$ consists of the ratios $x/y$ of Laurent series over $A$ with $y$ of non-zero reduction; the other rings are its pullbacks along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for suitable $\gamma \in \Gamma_0(M')$; injectivity; permutation of the family by all such pullbacks) and to the supersingular hypotheses (each $O_{\mathrm{SS}}\,s$ meets $\overline{\mathbb{Q}}$ in $A$; functions in $R_0.\mathrm{integers}$ regular wherever $\hat\jmath$ is and with reduction integral at $s$ lie in $O_{\mathrm{SS}}\,s$ and are congruent modulo its maximal ideal to any $a \in A$ whose residue is the value at $s$ of their reduction; invariance of $O_{\mathrm{SS}}\,s$ under the same pullbacks; existence of $t \in O_{\mathrm{SS}}\,s$ with $t - a$ a unit for all $a \in A$), all summarised here. Fix further a subfield $K_0 \subseteq \overline{\mathbb{Q}}$ with $\overline{\mathbb{Q}}/K_0$ algebraic and $\pi \in K_0$, a henselian discrete valuation domain $A_0$ with an injective local homomorphism $\iota : A_0 \to A$ whose image is $A \cap K_0$, with $\mathrm{residue} \circ \iota$ surjective and with uniformiser $\varpi_0$ satisfying $\iota(\varpi_0) = \pi$; the subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$, which contains the element $\hat\jmath$ coming from the $q$-expansion $\mathrm{jq}$ and is an $A_0$-algebra via $\iota$, with $\hat\jmath \neq 0$. Let $\mathfrak{n}$ be a maximal ideal of $\mathrm{TwoChartIntegralModel.chartAlgFin}\,A_0\,F_0\,\hat\jmath$, the subalgebra of elements of $F_0$ integral over $A_0[\hat\jmath]$, containing the image of $\varpi_0$, and suppose that for some $s \in W$ every element of this algebra whose image lies in the maximal ideal of $O_{\mathrm{SS}}\,s$ lies in $\mathfrak{n}$. Then for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the chart algebra to $\Omega$ with kernel $\mathfrak{n}$, the element $\varphi(\hat\jmath)$ lies in $\mathrm{ssJSet}\,q\,\Omega$: every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(\hat\jmath)$ has no non-zero point killed by $q$.
--
--   This is the converse implication to the statement that a closed special point of the descended two-chart model lying over a supersingular place is a Drinfeld centre: centring at such a place forces the $j$-value of the point to be supersingular, in the sense of Katz–Mazur 13.7.6. It is used in the assembly of the dichotomy for the descended model, in [`ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent`](thm.html#ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent), to rule out centres whose $j$-value is not supersingular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent.lean

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

theorem ModularCurve.FullLevel.mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent
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
    (𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫 : 𝔫.IsMaximal)
    (hϖ : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫)
    (s : ↥W)
    (hs : ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) → g ∈ 𝔫)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* Ω) (hφ : RingHom.ker φ = 𝔫) :
    φ (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ∈ ModularCurve.ssJSet q Ω := by sorry
