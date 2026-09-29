-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent
-- name    : ModularCurve.FullLevel.exists_valuationSubring_localization_chartAlg_of_not_mem_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/24f0f9fa-6f8f-58be-8a3c-26d071b4e133
-- title:
--   Localisations of the descended chart algebra are valuation rings
-- statement:
--   Fix a prime $q\ge 5$ and $M'\ge 1$ with $q\nmid M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ in which $q$ is a non-unit, and a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$ whose members are exactly the supersingular places (rational, affine geometric, with value of the geometric $j$-generator in the supersingular $j$-set for $q$). Assume `modularFunctionFieldBar M' ≤ fieldBar q M'` inside the Laurent series over $\overline{\mathbb Q}$, and let $R_0$ be a `ConstantReduction` of `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'` relative to $A$, compatible with coefficientwise reduction of Laurent series having coefficients in $A$. Let $\pi\in A$ satisfy $\pi^{q^2-1}=q$, let $\zeta$ be an element of `Idx q`, and let $O_{\mathrm{Ig}}$, indexed by $\mathbb P^1(\mathbb Z/q)$, and $O_{\mathrm{ss}}$, indexed by $W$, be families of valuation subrings of `fieldBar q M'` subject to: the Igusa conditions (membership in $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ is being a quotient of Laurent series with coefficients in $A$ whose denominator has non-zero reduction; transitivity of the $\Gamma_0(M')$-action through `redQ` and `levelAutBar`; injectivity; permutation of the family under every `levelAutBar`), and the supersingular conditions (constants in $O_{\mathrm{ss}}(s)$ are exactly those from $A$; elements of `R₀.integers` regular wherever $\hat\jmath$ is and whose $R_0$-residue is $s$-integral land in $O_{\mathrm{ss}}(s)$, congruent modulo its maximal ideal to any $a\in A$ whose residue is the $s$-value of that residue; invariance under `levelAutBar` for $\gamma\in\Gamma_0(M')$; existence of an element all of whose translates by elements of $A$ are units) — these hypotheses are summarised here. Let $K_0\subseteq\overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}$ algebraic over it and $\pi\in K_0$; let $A_0$ be a henselian discrete valuation ring with an injective local homomorphism $\iota:A_0\to A$ whose image in $\overline{\mathbb Q}$ is $A\cap K_0$, inducing a surjection onto the residue field of $A$, and with uniformiser $\varpi_0$ such that $\iota(\varpi_0)=\pi$. Let $F_0$ be the subfield of `fieldBar q M'` of elements all of whose Laurent coefficients lie in $K_0$, assume the image $\hat\jmath$ of `jq` lies in $F_0$ and is non-zero, and that the $A_0$-algebra structure on $F_0$ is the one induced by $\iota$. Let $S$ be $\{\hat\jmath\}$ or $\{\hat\jmath^{-1}\}$, and let $\mathfrak p$ be a non-zero prime ideal of $C=$ `TwoChartIntegralModel.chartAlg A₀ F₀ S`, the subalgebra of elements of $F_0$ integral over $A_0[S]$, with the image of $\varpi_0$ not in $\mathfrak p$. Then there is a valuation subring $V_1$ of $F_0$ whose elements are exactly the $f\in F_0$ admitting $b,c\in C$ with $c\notin\mathfrak p$ and $fc=b$; that is, the localisation $C_{\mathfrak p}$, taken inside $F_0$, is a valuation ring.
--
--   This records that on the generic fibre the descended chart algebra behaves like a Dedekind domain: away from the uniformiser $\varpi_0$ its localisations at non-zero primes are valuation rings of $F_0$. It supplies the valuation-ring input at generic primes to [`ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent`](thm.html#ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent), in the construction of a good chart for the full-level modular curve over a henselian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

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

theorem ModularCurve.FullLevel.exists_valuationSubring_localization_chartAlg_of_not_mem_descent
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
    (S : Set ↥F₀) (hS : S = {(⟨_, hjF₀⟩ : ↥F₀)} ∨ S = {(⟨_, hjF₀⟩ : ↥F₀)⁻¹})
    (𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S)) (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (hϖ : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S) ϖ₀ ∉ 𝔭) :
    ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S), c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀) := by sorry
