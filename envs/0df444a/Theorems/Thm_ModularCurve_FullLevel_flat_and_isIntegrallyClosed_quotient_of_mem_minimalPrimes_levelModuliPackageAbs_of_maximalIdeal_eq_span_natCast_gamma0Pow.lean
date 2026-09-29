-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_flat_and_isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_of_maximalIdeal_eq_span_natCast_gamma0Pow
-- name    : ModularCurve.FullLevel.flat_and_isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_of_maximalIdeal_eq_span_natCast_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/1628c556-bbff-5fd0-ac34-1e444d6c8d5b
-- title:
--   Flatness and normal components of the full-level moduli ring
-- statement:
--   Fix a prime $q$ with $q\ge 5$, a prime $\ell$ with $\ell\ge 3$ and $\ell\neq q$, and a nonzero natural number $M'$ with $q\nmid M'$. Let $A_0$ be a discrete valuation domain whose maximal ideal is $(q)$ and whose residue field is finite. Assume: (i) for every $A_0$-algebra $T$, level-$\ell$ data $D=(x_P,y_P,x_Q,y_Q)$ satisfying `IsLevelPStructure` for $W$ (both points satisfy the affine equation of $W$, $\mathrm{preΨ}_\ell$ vanishes at $x_P$ and $x_Q$, and both elements `indepElt` are units) continue to satisfy it for $C\bullet W$ after the variable change $D\mapsto D.\mathrm{variableChange}\,C$; (ii) correspondingly, `IsGamma0PowAt W p k h` (the two-torsion condition `IsTwoKernel` when $p^k=2$, otherwise `IsCyclicGenKernel`: $\deg h\le\varphi(p^k)/2$, leading coefficient $1$, $h\cdot \mathrm{preΨ}_{p^{k-1}}\mid \mathrm{preΨ}_{p^k}$, and $h$ divides the relevant `smulNumerator`s) is preserved by `kernelVariableChangeDeg`; (iii) $\mathcal G$ is a family of relative group laws on the graded projective models of Weierstrass curves with unit discriminant, which is chord–tangent (on fields its points are computed by an additive, Galois-equivariant bijection with the affine point group) and has the origin as identity (the identity section factors through the origin chart, killing $x/y$ and $z/y$); (iv) $\mathcal T$ is a transport of raw Drinfeld pairs along $A_0$-algebra maps and variable changes, preserving the Drinfeld-basis condition at level $q$, and satisfying `IsSectionTransport`, i.e. its action and functoriality are computed by composing the sections with the induced maps on $\mathrm{Proj}$; (v) variable changes and coefficient maps of projective models are realised by graded ring homomorphisms $\varphi$ whose images dominate the irrelevant ideal, in the senses `IsVariableChangeHom` and `IsCoefficientHom`. Let $P_0$ be a representing package for the level moduli datum attached to `rigidDataPow A₀ ℓ M' q` (the product of the $\Gamma_0(M')$ prime-power kernel component, the level-$\ell$ component and the Drinfeld level-$q$ component), that is, an $A_0$-algebra $B_0$ with a universal point such that every point over any $A_0$-algebra $T$ is the image of the universal point under a unique $A_0$-algebra map $B_0\to T$; assume $B_0$ is of finite type over $A_0$. Then $B_0$ is flat as an $A_0$-module, and for every minimal prime $\mathfrak P$ of the zero ideal of $B_0$ the quotient $B_0/\mathfrak P$ is integrally closed.
--
--   This is the normality-and-flatness statement for the fine moduli ring of elliptic curves with $\Gamma_0(M')$-, full level-$\ell$- and Drinfeld level-$q$-structure over an unramified base with uniformiser $q$: the components of $\operatorname{Spec} B_0$ are normal integral schemes and $B_0$ is flat over the base, in the form used further on to produce roots of unity in the quotients by minimal primes and to supply flatness of the full-level moduli ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_flat_and_isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_of_maximalIdeal_eq_span_natCast_gamma0Pow.lean

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

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.flat_and_isIntegrallyClosed_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_of_maximalIdeal_eq_span_natCast_gamma0Pow
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
    [Algebra.FiniteType A₀ P₀.B₀] :
    Module.Flat A₀ P₀.B₀ ∧ ∀ 𝔓 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes, IsIntegrallyClosed (P₀.B₀ ⧸ 𝔓) := by sorry
