-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_isModuliRelabelling_rigidDataH1Pow
-- name    : ModularCurve.LevelRelabelling.exists_isModuliRelabelling_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/5eaf796e-025c-5ca3-8058-05864079fcd9
-- title:
--   Diamond relabelling by Γ₀(M') on `rigidDataH1Pow`
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number, and $\ell$ a prime with $3\le\ell$ and $\ell\mid M'$. Let $A$ be a commutative ring in which $\ell$ is a unit, and assume: `hℓ`, that `IsGamma1Point` for $\ell$ is preserved by the variable-change action on `LevelPData`; `hM`, that `IsGamma0PowAt` for $p^k$ is preserved by `kernelVariableChangeDeg` with degree `gamma0PowDeg p k`; `hL`, that divisibility of `inLineMulPoly W ℓ n x` by $h$ passes to `kernelVariableChangeDeg C d h` dividing `inLineMulPoly (C • W) ℓ n (u⁻¹² (x - C.r))`; a family of relative group laws $\mathcal G$ on the projective models of curves with unit discriminant that is chord–tangent and has the origin as identity; a level transport $\mathcal T$ for $\mathcal G$ and $q$ satisfying `IsSectionTransport`; and `hVC`, `hCO`, realising every variable change and every coefficient $A$-algebra map by graded ring maps of the projective-model gradings satisfying `IsVariableChangeHom`, respectively `IsCoefficientHom`, and pulling the irrelevant ideal back appropriately. Write $\mathcal D$ for `rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯`, whose raw objects over an $A$-algebra $T$ consist of a Weierstrass curve with unit discriminant together with a triple: a family of $\Gamma_0(p^{v_p(M')})$-generator kernel polynomials indexed by the prime factors of $M'$, a $\Gamma_1(\ell)$-point datum, and a raw Drinfeld pair forming a Drinfeld basis of level $q$, subject to the linking condition `IsGamma1Link`; its points over $T$ are the raw objects modulo the variable-change action. The assertion is that there is a map $\rho$ from $\Gamma_0(M')$ to the automorphisms of the associated level moduli datum (endomorphisms of points, natural in $T$ and preserving the $j$-invariant) with the following four properties. First, over any field $T$ that is an $A$-algebra, if $x,x'$ are raw objects, the discriminant of the curve carried by the Drinfeld component of $x$ is a unit, $x'$ and $x$ have the same curve and the same $\Gamma_0$-tuple, the point of the base change of $x.curve$ to $T$ attached by `toPoint` to the coordinates $x'.xP,x'.yP$ equals $\gamma_{00}$ times the point attached to $x.xP,x.yP$, the $Q$-coordinates of $x'$ coincide with its $P$-coordinates, and the Drinfeld component of $x'$ is `RawDrinfeldPair.relabel` of that of $x$ by the integral matrix $\gamma$, then $\rho(\gamma)$ sends the class of $x$ to the class of $x'$. Second, $\rho(\gamma\gamma')$ acts as $\rho(\gamma)$ followed by $\rho(\gamma')$ on points over every $A$-algebra, so $\rho$ is an anti-homomorphism. Third, $\rho(1)$ acts as the identity. Fourth, $\rho(\gamma^{-1})$ and $\rho(\gamma)$ are mutually inverse on points over every $A$-algebra.
--
--   This is the diamond-operator relabelling of level structures in the Katz–Mazur style: the $\Gamma_0(M')$-tuple of kernel polynomials is left fixed, the $\Gamma_1(\ell)$-point is multiplied by the upper-left entry of $\gamma$ (a unit modulo $\ell$ since $\ell\mid M'$ and the lower-left entry is divisible by $M'$) and kept as a coincident pair, while the Drinfeld basis of level $q$ is relabelled by $\gamma$. It supplies the group action used in identifying the level automorphism attached to Tate points and in building the level moduli package for `rigidDataH1Pow`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_isModuliRelabelling_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.LevelRelabelling.exists_isModuliRelabelling_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓg : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
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
        IsCoefficientHom W f.toRingHom φ) :
    ∃ ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut,

      (∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [DecidableEq T] [Algebra A T]
      (x x' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
      x'.curve = x.curve →
      x'.level.1 = x.level.1 →
      ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange T) x'.level.2.1.xP x'.level.2.1.yP =
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
          ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange T) x.level.2.1.xP x.level.2.1.yP →
      x'.level.2.1.xQ = x'.level.2.1.xP → x'.level.2.1.yQ = x'.level.2.1.yP →
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
      (ρ γ).act (Quot.mk _ x) = Quot.mk _ x') ∧

      (∀ (γ γ' : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [CommRing T] [Algebra A T]
        (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ (γ * γ')).act x = (ρ γ').act ((ρ γ).act x)) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ 1).act x = x) ∧
      (∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [CommRing T] [Algebra A T]
        (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ γ⁻¹).act ((ρ γ).act x) = x ∧ (ρ γ).act ((ρ γ⁻¹).act x) = x) := by sorry
