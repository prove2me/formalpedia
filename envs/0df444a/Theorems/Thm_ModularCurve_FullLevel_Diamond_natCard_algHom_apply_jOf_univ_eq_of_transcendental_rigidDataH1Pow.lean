-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_natCard_algHom_apply_jOf_univ_eq_of_transcendental_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.natCard_algHom_apply_jOf_univ_eq_of_transcendental_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/4fbd50c3-2deb-5169-8774-55f1426f0a3c
-- title:
--   Count of H₁-moduli points above a transcendental j
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $A$ be a commutative ring in which the images of $\ell_g$ and of $M'$ are units. Three equivariance hypotheses are assumed for all $A$-algebras $T$: `hℓ`, that a `LevelPData` $D$ satisfying `IsGamma1Point` for $W$ and $\ell_g$ (that is, $(D.xP,D.yP)$ satisfies the affine Weierstrass equation, $\mathrm{pre}\Psi_{\ell_g}$ vanishes at $D.xP$, and $(D.xQ,D.yQ)=(D.xP,D.yP)$) transforms under a variable change $C$ into such a datum for $C \bullet W$; `hM`, that `IsGamma0PowAt W p k h` is preserved when $h$ is replaced by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and `hL`, that divisors of `inLineMulPoly W ℓg n x` are carried by `kernelVariableChangeDeg C d` to divisors of `inLineMulPoly (C • W) ℓg n ((C.u⁻¹)^2 (x - C.r))`. Further data: group laws $\mathcal{G}$ on the projective Weierstrass models over $A$-algebras which are chord–tangent and have the origin as identity, a level transport $\mathcal{T}$ at $q$ for Drinfeld pairs which is a section transport, and the existence (`hVC`, `hCO`) of graded ring homomorphisms between the projective model gradings realising variable changes and coefficient maps, each pulling the irrelevant ideal back appropriately. Let $P_0$ be a package consisting of an $A$-algebra $B_0$ together with a point $\mathrm{univ}$ over $B_0$ which represents, by unique $A$-algebra homomorphisms, the moduli datum attached to `rigidDataH1Pow A ℓg M' q …`: its points over $T$ are variable-change classes of tuples consisting of a Weierstrass curve with unit discriminant, a family of cyclic kernel generators at each prime power $p^{v_p(M')}$, a $\Gamma_1(\ell_g)$-point, and a Drinfeld basis of level $q$, linked by the condition that the $\ell_g$-component of the kernel family divide `inLineMulPoly W ℓg (ℓg ^ (M'.factorization ℓg - 1)) D.xP`; the $j$-map sends a class to the $j$-invariant of its curve. Finally let $\Omega$ be an algebraically closed $A$-algebra field of characteristic $0$ with $q \neq 0$ in $\Omega$, and let $t \in \Omega$ be transcendental over $\mathbb{Q}$. Then the number of $A$-algebra homomorphisms $\varphi : B_0 \to \Omega$ with $\varphi(j(\mathrm{univ})) = t$ equals $\bigl(\prod_{p \mid M'} p^{v_p(M')-1}(p+1)\bigr)(\ell_g - 1)\,\#\mathrm{GL}_2(\mathbb{Z}/q)$ divided by $2$ (division in $\mathbb{N}$).
--
--   This is the degree computation for the fine moduli ring of the composite level structure ($\Gamma_0(M')$ prime-power kernels, a linked $\Gamma_1(\ell_g)$-point, and a Drinfeld basis of level $q$) over a transcendental $j$-line point: the fibre count is $\psi(M')(\ell_g-1)\#\mathrm{GL}_2(\mathbb{Z}/q)/2$, the factor $2$ reflecting the generic automorphism $\pm 1$ of an elliptic curve with $j \neq 0, 1728$. It feeds the statement that the fraction field of the base change of the moduli ring is reduced of the expected rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_natCard_algHom_apply_jOf_univ_eq_of_transcendental_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.natCard_algHom_apply_jOf_univ_eq_of_transcendental_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : Type) [CommRing A]
    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
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
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (t : Ω) (ht : Transcendental ℚ t) :
    Nat.card {φ : P₀.B₀ →ₐ[A] Ω // φ ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) = t} =
      (∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1)) *
        (ℓg - 1) * Nat.card (GL (Fin 2) (ZMod q)) / 2 := by sorry
