-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_formallySmooth_localization_atPrime_of_not_mem_levelModuliPackageAbs_gamma0Pow
-- name    : ModularCurve.FullLevel.formallySmooth_localization_atPrime_of_not_mem_levelModuliPackageAbs_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/36077dc8-0760-5821-bf82-68231b01ebc1
-- title:
--   Formal smoothness of the full-level moduli ring away from q
-- statement:
--   Fix a prime $q\ge 5$, a prime $\ell\ge 3$ with $\ell\ne q$, and a natural number $M'\ne 0$ with $q\nmid M'$. Let $A_0$ be a discrete valuation domain whose maximal ideal is $(q)$ and whose residue field is finite. Assume two equivariance statements for all $A_0$-algebras $T$: that a Weierstrass variable change $C$ carries a level-$\ell$ datum $D$ (four coordinates with `IsLevelPStructure`: both points satisfy the affine equation, both $x$-coordinates are roots of $\Psi_\ell$-type polynomial `preΨ`, and the two independence elements are units) to `D.variableChange C`, and that it carries a polynomial $h$ with `IsGamma0PowAt W p k h` to `kernelVariableChangeDeg C (gamma0PowDeg p k) h`. Let $\mathcal G$ be a family of relative group laws on the projective Weierstrass models of discriminant-unit curves, chord-tangent and with origin as identity, and $\mathcal T$ a level transport for $\mathcal G$ at $q$ satisfying `IsSectionTransport`; assume also that graded variable-change and coefficient homomorphisms as in `IsVariableChangeHom` and `IsCoefficientHom` exist, with the irrelevant-ideal condition. Let $P_0$ be a package representing the moduli datum of `rigidDataPow A₀ ℓ M' q`, the rigidification of the product of the $\Gamma_0$-prime-power component (tuples of kernel polynomials indexed by the prime factors of $M'$), the level-$\ell$ component and the Drinfeld-$q$ component, with $B_0:=P_0.B_0$ of finite type over $A_0$. Then for every maximal ideal $\mathfrak m$ of $B_0$ with $q\notin\mathfrak m$, the localisation $(B_0)_{\mathfrak m}$ is formally smooth over $A_0$.
--
--   This is the smoothness of the fine full-level moduli ring at closed points of the generic fibre, in the style of Katz–Mazur: away from the residue characteristic $q$ the three level structures lift uniquely along nilpotent thickenings, so the localised moduli ring is formally smooth over the base. It feeds the proof that the completions of this ring at such points are integrally closed domains.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_formallySmooth_localization_atPrime_of_not_mem_levelModuliPackageAbs_gamma0Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.formallySmooth_localization_atPrime_of_not_mem_levelModuliPackageAbs_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    [NeZero M'] (hM'q : ¬ q ∣ M')

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Finite (ResidueField A₀)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A₀ P₀.B₀]
    (𝔪 : Ideal P₀.B₀) [𝔪.IsMaximal] (hq𝔪 : algebraMap A₀ P₀.B₀ (q : A₀) ∉ 𝔪) :
    Algebra.FormallySmooth A₀ (Localization.AtPrime 𝔪) := by sorry
