-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_isModuliRelabelling_gamma0Pow
-- name    : ModularCurve.LevelRelabelling.exists_isModuliRelabelling_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/c9f49e01-e774-5022-81d7-58ee55b4703e
-- title:
--   Relabelling action of Γ₀(M') on the rigidified moduli problem
-- statement:
--   Fix primes $q$ and $\ell$ with $\ell\ge 3$, a natural number $M'\neq 0$, and a commutative ring $A$ in which $\ell$ is invertible. Assume: `hℓ`, that a Katz level-$\ell$ datum (four coordinates satisfying the Weierstrass equation, killed by `preΨ` $\ell$, with the two independence elements units) stays such a datum after a variable change; `hM`, that the predicate `IsGamma0PowAt` at $p^k$ is preserved by $C\mapsto$ `kernelVariableChangeDeg`; $\mathcal G$ a family of relative group laws on the projective models of Weierstrass curves of unit discriminant over $A$-algebras, assumed chord–tangent (`h𝒢`) and with the origin as identity (`h𝒢O`); $\mathcal T$ a level transport for $\mathcal G$ at $q$ with `IsSectionTransport` (`h𝒯`); and `hVC`, `hCO`, the existence, for every variable change and every $A$-algebra map, of graded ring homomorphisms of the projective coordinate rings realising it in the sense of `IsVariableChangeHom`, `IsCoefficientHom`, and compatible with irrelevant ideals. Then there is a map $\rho$ from $\Gamma_0(M')$ to the automorphisms of the moduli problem `(rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum` (self-maps of the points over each $A$-algebra, natural in the algebra and fixing the $j$-invariant) such that: over a field, if raw data $x'$ and $x$ have the same curve and same $\Gamma_0$-power polynomials, while the level-$\ell$ datum and the Drinfeld pair of $x'$ are the relabellings of those of $x$ by the integral matrix of $\gamma$ (via `LevelPData.relabel` and `RawDrinfeldPair.relabel`), then $\rho(\gamma)$ carries the class of $x$ to the class of $x'$; $\rho(\gamma\gamma')$ acts as $\rho(\gamma')$ after $\rho(\gamma)$; $\rho(1)$ is the identity; and $\rho(\gamma^{-1})$ is a two-sided inverse of $\rho(\gamma)$ on the points over every $A$-algebra.
--
--   This realises the classical right action of $\Gamma_0(M')$ by relabelling of level structures as automorphisms of the rigidified full-level moduli problem carrying a $\Gamma_0(M')$-tuple of cyclic-kernel polynomials, a Katz level-$\ell$ structure and a Drinfeld basis at $q$. It feeds the identification of level automorphisms on charts, the supersingular-fibre dictionary and the stabiliser computations used later in the construction of the modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_isModuliRelabelling_gamma0Pow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.LevelRelabelling.exists_isModuliRelabelling_gamma0Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
        IsCoefficientHom W f.toRingHom φ) :
    ∃ ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut,

      (∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [Algebra A T]
        (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
        x'.curve = x.curve →
        x'.level.1 = x.level.1 →
        x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
        x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
        (ρ γ).act (Quot.mk _ x) = Quot.mk _ x') ∧

      (∀ (γ γ' : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [CommRing T] [Algebra A T]
        (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ (γ * γ')).act x = (ρ γ').act ((ρ γ).act x)) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ 1).act x = x) ∧
      (∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [CommRing T] [Algebra A T]
        (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ γ⁻¹).act ((ρ γ).act x) = x ∧ (ρ γ).act ((ρ γ⁻¹).act x) = x) := by sorry
