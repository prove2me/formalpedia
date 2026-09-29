-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algHom_dualNumber_fst_eq_snd_ne_zero_of_exists_pt_dualNumber_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_algHom_dualNumber_fst_eq_snd_ne_zero_of_exists_pt_dualNumber_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/8b7a7e34-ae18-539f-9b82-e3f438b37cfa
-- title:
--   Non-constant dual-number point yields a non-zero tangent vector
-- statement:
--   Fix primes $q \ge 5$ and $\ell \ge 3$ with $\ell \ne q$, and a nonzero $M'$ divisible by neither $q$ nor $\ell$; let $A$ be a commutative ring in which $\ell$ and $M'$ are units. Assume: the stability hypotheses $h\ell$ and $hM$, saying that a level-$\ell$ Katz structure (`IsLevelPStructure`: two points on the affine model, both with $x$-coordinate a root of $\mathrm{pre}\Psi_\ell$ and with both independence elements units) and the property `IsGamma0PowAt` at $(p,k)$ of a polynomial are preserved by variable change, in the transported forms `LevelPData.variableChange` and `kernelVariableChangeDeg`; group laws $\mathcal G$ on the projective models of discriminant-unit curves that are chord–tangent and have the origin as identity; a level transport $\mathcal T$ for Drinfeld $q$-bases which is a section transport; and hypotheses $hVC$, $hCO$ providing graded ring homomorphisms of the projective-model rings realising variable change and coefficient change. Let $P_0$ be a fine moduli package for the moduli datum of `rigidDataPow A ℓ M' q`, i.e. an $A$-algebra $B_0$ with a universal point such that every point over an $A$-algebra $T$ is uniquely $\mathrm{map}\,\varphi$ of it. Let $\Omega$ be an algebraically closed field of characteristic zero over $A$ with $q \ne 0$ in $\Omega$, and $\varphi_0 : B_0 \to_A \Omega$. If some point $y$ over the dual numbers $\Omega[\varepsilon]$ satisfies $\mathrm{fst}_*y = (\varphi_0)_*\mathrm{univ}$ and $y \ne \mathrm{inl}_*(\varphi_0)_*\mathrm{univ}$, then there is $\varphi : B_0 \to_A \Omega[\varepsilon]$ whose first component is $\varphi_0$ on every element and whose $\varepsilon$-component is non-zero at some element.
--
--   This is the infinitesimal form of representability for the rigidified moduli problem of elliptic curves with $\Gamma_0$-type kernel data at the primes dividing $M'$, a Katz level-$\ell$ structure and a Drinfeld $q$-basis: a first-order deformation of a point that is not the constant one produces a tangent vector of the coarse parameter ring $B_0$ at that point. It feeds the non-triviality step used in the study of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algHom_dualNumber_fst_eq_snd_ne_zero_of_exists_pt_dualNumber_gamma0Pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_algHom_dualNumber_fst_eq_snd_ne_zero_of_exists_pt_dualNumber_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (A : Type) [CommRing A]
    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (φ₀ : P₀.B₀ →ₐ[A] Ω)

    (hy : ∃ y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt (DualNumber Ω),
      (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A) y = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φ₀ P₀.univ ∧
      y ≠ (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A) ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φ₀ P₀.univ)) :
    ∃ φ : P₀.B₀ →ₐ[A] DualNumber Ω,
      (∀ b : P₀.B₀, (φ b).fst = φ₀ b) ∧ ∃ b : P₀.B₀, (φ b).snd ≠ 0 := by sorry
