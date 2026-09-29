-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/a4d70a8a-333d-583c-9945-4f7fae8834a1
-- title:
--   Descent of full-level K-points to a discrete valuation ring
-- statement:
--   Let $A$ be a commutative ring, let $q$ and $\ell$ be primes and $M'$ a nonzero natural number, with $\ell \ge 3$ and with $\ell$, $M'$, $2$ and $3$ units in $A$. Assume two equivariance realisers: `hℓ` says that for every $A$-algebra $T$, every Weierstrass curve $W/T$, every variable change $C$ and every quadruple $D=(x_P,y_P,x_Q,y_Q)$ of elements of $T$, if $D$ is a level-$\ell$ structure on $W$ (both points satisfy the affine equation, $\mathrm{pre}\Psi_\ell$ vanishes at $x_P$ and at $x_Q$, and the two independence elements $\prod_{1\le a\le(\ell-1)/2}(x\,\Psi_a^2(x_0)-\Phi_a(x_0))$ are units) then the transformed quadruple $D.\mathrm{variableChange}\,C$ is a level-$\ell$ structure on $C \bullet W$; `hM` says that the predicate `IsGamma0PowAt` at $(p,k)$ — the two-kernel condition when $p^k=2$, and otherwise the cyclic-generator-kernel condition on a monic-in-degree-$\varphi(p^k)/2$ polynomial $h$ dividing into $\mathrm{pre}\Psi_{p^k}$ and into the relevant $\Psi$-numerators — is preserved by $h \mapsto \mathrm{kernelVariableChangeDeg}\,C\,(\mathrm{gamma0PowDeg}\,p\,k)\,h$. Assume further a family $\mathcal{G}$ of relative group laws on the projective models of discriminant-unit Weierstrass curves over $A$-algebras which is chord-tangent and has the origin as identity, a level transport $\mathcal{T}$ for raw Drinfeld pairs at level $q$ satisfying `IsSectionTransport`, and realiser hypotheses `hVC`, `hCO` producing graded ring homomorphisms between projective-model graded rings that implement a variable change, respectively a change of coefficients along an $A$-algebra map, each dominating the irrelevant ideal. Let $K$ be a field that is an $A$-algebra, and $R₀$ a discrete valuation domain that is an $A$-algebra with $K$ as its fraction field, compatibly. Write $D$ for the moduli datum of the rigid Weierstrass data `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯`, whose $T$-points are variable-change classes of tuples consisting of a Weierstrass curve over $T$ with unit discriminant, a family of $\Gamma_0$-kernel polynomials indexed by the prime factors $p$ of $M'$ at exponent $v_p(M')$, a level-$\ell$ structure, and a raw Drinfeld pair at level $q$ which is a Drinfeld basis for $\mathcal{G}$. Then for every $x \in D.\mathrm{Pt}(K)$ whose $j$-invariant $D.\mathrm{jOf}\,x$ lies in the image of $R₀ \to K$, there is $y \in D.\mathrm{Pt}(R₀)$ with $D.\mathrm{map}$ along $R₀ \to K$ sending $y$ to $x$.
--
--   This is the point-level form of the valuative criterion for the full-level moduli problem over the $j$-line: a $K$-point with integral $j$-invariant extends to a point over the discrete valuation ring. It is used to show that the absolute level-moduli package takes values in the valuation subring in the presence of integral $j$ and of invertibility of $2$, $3$, $\ell$ and $M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_gamma0Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem ModularCurve.FullLevel.exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_gamma0Pow
    (A : Type u) [CommRing A] (q ℓ M' : ℕ) [Fact q.Prime] [Fact ℓ.Prime] [NeZero M']
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'u : IsUnit ((M' : ℕ) : A))
    (h2A : IsUnit ((2 : ℕ) : A)) (h3A : IsUnit ((3 : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (K : Type u) [Field K] [Algebra A K]
    (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra A R₀] [Algebra R₀ K]
    [IsScalarTower A R₀ K] [IsFractionRing R₀ K]
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt K)
    (hx : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x ∈ Set.range (algebraMap R₀ K)) :
    ∃ y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt R₀,
      (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (IsScalarTower.toAlgHom A R₀ K) y = x := by sorry
