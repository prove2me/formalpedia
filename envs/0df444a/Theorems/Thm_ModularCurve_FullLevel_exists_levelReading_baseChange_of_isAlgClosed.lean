-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed
-- name    : ModularCurve.FullLevel.exists_levelReading_baseChange_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/2cacb4b1-7593-57bb-901e-35d153d5a6c0
-- title:
--   Reading rigid full-level structures as point-level data, Galois-equivariantly
-- statement:
--   Fix a prime $q$, a nonzero natural number $M'$, a prime $\ell \ge 3$, and a commutative ring $A$. Assume two equivariance hypotheses: `hℓ`, that for every $A$-algebra $T$, Weierstrass curve $W/T$, variable change $C$ and datum $D=(x_P,y_P,x_Q,y_Q)$, the conjunction of conditions `IsLevelPStructure W ℓ D` (both points satisfy the affine Weierstrass equation, $\mathrm{pre}\Psi_\ell$ vanishes at $x_P$ and at $x_Q$, and the two elements $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q=\prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,\Psi^2_a(x_P)-\Phi_a(x_P)\bigr)$ and its transpose are units) is inherited by $C\bullet W$ with $D$ transformed by $C$; and `hM`, that `IsGamma0PowAt W p k h` (the condition `IsTwoKernel` if $p^k=2$, else `IsCyclicGenKernel p k`) is inherited by $C\bullet W$ with $h$ replaced by $\mathrm{kernelVariableChangeDeg}\,C\,(\mathrm{gamma0PowDeg}\,p\,k)\,h$. Fix further a family $\mathcal G$ of relative group laws on the graded projective models of Weierstrass curves with unit discriminant over $A$-algebras, satisfying the chord–tangent condition (existence of a points-evaluation bijection additive for $\mathcal G$ and compatible with Galois twisting) and the origin condition (the identity section is cut out by a chart homomorphism killing $x/y$ and $z/y$); a Drinfeld level-$q$ transport datum $\mathcal T$ for $\mathcal G$ satisfying the section-transport condition; and hypotheses `hVC`, `hCO` providing, for each variable change and each coefficient map, a graded ring homomorphism of projective-model rings realising it and dominating the irrelevant ideal. Let $\Omega$ be an algebraically closed field of characteristic zero over $A$, let $K_0$ be a field over $A$ with $\Omega$ a $K_0$-algebra compatibly with $A$, and let $E$ be an elliptic Weierstrass curve over $K_0$. Write $L$ for the product level component $\mathrm{gamma0PowComponent}\,A\,M'\,hM \times (\mathrm{levelPComponent}\,A\,\ell\,h\ell \times \mathrm{levelComponent}\,A\,\mathcal G\,q\,\mathcal T)$, whose $\Omega$-points are triples consisting of a family of polynomials indexed by the prime factors of $M'$, a datum $D$ of four coordinates, and a raw Drinfeld pair. The assertion is that there exists a map $\Theta$ from $L(\Omega)$ to $\bigl((E_\Omega(\Omega)\times E_\Omega(\Omega))\times(E_\Omega(\Omega)\times E_\Omega(\Omega))\bigr)\times \{\text{subgroups of }E_\Omega(\Omega)\}$, where $E_\Omega$ is the base change of $E$ to $\Omega$, such that for every $\beta \in L(\Omega)$ which is a level structure on $E_\Omega$ in the sense of $L$ (each polynomial satisfies `IsGamma0PowAt` at the corresponding prime power dividing $M'$; $D$ is a level-$\ell$ structure; and the Drinfeld pair has underlying curve the projective model of $E_\Omega$, with unit discriminant, its two sections forming a Drinfeld basis for $\mathcal G$ at level $q$), the value $\Theta\beta=((P_1,P_2),(Q_1,Q_2),C)$ satisfies: $\ell P_1=\ell P_2=0$ and $aP_1+bP_2=0$ forces $\ell \mid a$ and $\ell \mid b$; $qQ_1=qQ_2=0$ and $aQ_1+bQ_2=0$ forces $q \mid a$ and $q \mid b$; $C$ is cyclic with $\#C=M'$; and for every $\sigma \in \mathrm{Aut}(\Omega/K_0)$, $\Theta$ of the image of $\beta$ under the functorial action of $\sigma$ (viewed as an $A$-algebra map) equals the componentwise image of $\Theta\beta$ under the induced map on points, with $C$ sent to its image subgroup.
--
--   This is the comparison, over an algebraically closed field of characteristic zero, between the level structures of the rigid $\Gamma_0(M')\times\Gamma(\ell)\times\Gamma(q)$ Weierstrass moduli problem and the naive level structures on the group of points: bases of the $\ell$- and $q$-torsion together with a cyclic subgroup of order $M'$, in a form equivariant for $\mathrm{Aut}(\Omega/K_0)$. It is the moduli-theoretic input to the bound [`ModularCurve.FullLevel.index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow`](thm.html#ModularCurve.FullLevel.index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow), where the Galois equivariance is what allows conjugates of a level structure to be counted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open ModularCurve

universe u

theorem ModularCurve.FullLevel.exists_levelReading_baseChange_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type u) [CommRing A]

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

    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] [Algebra A Ω]
    (K₀ : Type u) [Field K₀] [Algebra A K₀] [Algebra K₀ Ω] [IsScalarTower A K₀ Ω]
    (E : WeierstrassCurve K₀) [E.IsElliptic] :
    ∃ Θ : ((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).obj Ω →
        (((E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point) ×
          ((E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point)) ×
          AddSubgroup (E.baseChange Ω).toAffine.Point,
      ∀ β : ((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).obj Ω,
        ((ModularCurve.gamma0PowComponent A M' hM).prod
          ((ModularCurve.levelPComponent A ℓ hℓ).prod
            (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).IsLevel (E.baseChange Ω) β →

        (ℓ • (Θ β).1.1.1 = 0 ∧ ℓ • (Θ β).1.1.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.1.1 + b • (Θ β).1.1.2 = 0 → (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b) ∧

        (q • (Θ β).1.2.1 = 0 ∧ q • (Θ β).1.2.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.2.1 + b • (Θ β).1.2.2 = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧

        (IsAddCyclic (Θ β).2 ∧ Nat.card (Θ β).2 = M') ∧

        (∀ σ : Ω ≃ₐ[K₀] Ω,
          Θ (((ModularCurve.gamma0PowComponent A M' hM).prod
              ((ModularCurve.levelPComponent A ℓ hℓ).prod
                (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).map
              ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) β) =
            (((WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.1.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.1.2),
              (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.2)),
              ((Θ β).2).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω)))) := by sorry
