-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_natCard_algHom_apply_jOf_univ_eq_of_transcendental_gamma0Pow
-- name    : ModularCurve.FullLevel.natCard_algHom_apply_jOf_univ_eq_of_transcendental_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/32cad806-644c-5a9f-be60-c0623a1f0753
-- title:
--   Generic point count for the rigidified full-level problem
-- statement:
--   Fix a prime $q\ge 5$, a nonzero natural number $M'$ with $q\nmid M'$, and a prime $\ell\ge 3$ with $\ell\neq q$ and $\ell\nmid M'$, together with a commutative ring $A$ in which $\ell$ and $M'$ are invertible. Assume: the stability hypothesis `hℓ` that a Weierstrass variable change carries a level-$\ell$ Katz structure $(x_P,y_P,x_Q,y_Q)$ — both points satisfying the affine equation, $\mathrm{pre}\Psi_\ell$ vanishing at both $x$-coordinates, and both independence elements `indepElt` units — to the corresponding transformed datum; the stability hypothesis `hM` that variable changes carry `IsGamma0PowAt` kernel polynomials to their `kernelVariableChangeDeg` transforms; group laws $\mathcal G$ on the projective models over all $A$-algebras that are chord-tangent and have the origin as identity; a level transport $\mathcal T$ for Drinfeld pairs at $q$ satisfying `IsSectionTransport`; and the hypotheses `hVC`, `hCO` providing graded ring homomorphisms realising variable changes and coefficient maps on the graded projective model rings. Let $P_0$ be a fine moduli package for the rigid datum `rigidDataPow`, whose points over an $A$-algebra $T$ are Weierstrass curves over $T$ with unit discriminant equipped with a tuple of $\Gamma_0$-power kernel polynomials indexed by the prime factors of $M'$, a level-$\ell$ Katz datum and a Drinfeld pair at $q$, taken up to variable change; thus $P_0$ consists of an $A$-algebra $B_0$, a point `univ` over $B_0$, and the property that every point over every $A$-algebra $T$ is the image of `univ` under a unique $A$-algebra map $B_0\to T$. Let $\Omega$ be an algebraically closed field of characteristic zero, an $A$-algebra, with $q\neq 0$ in $\Omega$, and let $t\in\Omega$ be transcendental over $\mathbb Q$. Then the number of $A$-algebra homomorphisms $\varphi:B_0\to\Omega$ sending the $j$-invariant of `univ` to $t$ equals $$\Big(\prod_{p\mid M'}p^{v_p(M')-1}(p+1)\Big)\cdot\#\mathrm{GL}_2(\mathbb Z/\ell)\cdot\#\mathrm{GL}_2(\mathbb Z/q)\,/\,2,$$ the division being natural-number division.
--
--   This is the count of the geometric points of the fine moduli ring of the rigidified full-level problem lying over a transcendental $j$-invariant: the fibre has $\psi(M')\cdot\#\mathrm{GL}_2(\mathbb Z/\ell)\cdot\#\mathrm{GL}_2(\mathbb Z/q)/2$ points, the division by $2$ reflecting the automorphism $\pm 1$ of a curve with $j\neq 0,1728$. It feeds the determination of the rank and reducedness of $B_0$ over the function field of the $j$-line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_natCard_algHom_apply_jOf_univ_eq_of_transcendental_gamma0Pow.lean

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

theorem ModularCurve.FullLevel.natCard_algHom_apply_jOf_univ_eq_of_transcendental_gamma0Pow
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
    (t : Ω) (ht : Transcendental ℚ t) :
    Nat.card {φ : P₀.B₀ →ₐ[A] Ω // φ ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) = t} =
      (∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1)) *
        Nat.card (GL (Fin 2) (ZMod ℓ)) * Nat.card (GL (Fin 2) (ZMod q)) / 2 := by sorry
