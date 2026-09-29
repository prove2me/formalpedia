-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_level_snd_snd_act_mapRing_eq_relabel_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_level_snd_snd_act_mapRing_eq_relabel_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/9e378211-efb7-5e6a-bf38-46359bfa22b1
-- title:
--   Galois translate of the Tate point relabels its Drinfeld pair
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and a positive integer $M'$ divisible by neither; a characteristic-zero field $L$ carrying a primitive $(q\ell)$-th root of unity $\xi$ and a ring homomorphism $\iota_0\colon L\to\mathbb{C}$ with $\iota_0\xi=e^{2\pi i/(q\ell)}$; the intermediate field $K$ of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the function field of level $(q\ell)^2M'$ and group [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22) $(q\ell)\,M'$, the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$; a discrete valuation ring $A$ with fraction field $L$, with $q$ in its maximal ideal and $\ell$, $M'$ units, acting on $K$ compatibly; an element $j\in K$, nonzero, whose Laurent expansion is that of $j$; stability hypotheses `hℓ`, `hM` for level-$\ell$ data and $\Gamma_0$-power kernel polynomials under variable change; group laws $\mathcal{G}$ that are chord–tangent and origin-identity, a section transport $\mathcal{T}$ at $q$, and the existence hypotheses `hVC`, `hCO` of graded homomorphisms on projective models realising variable change and coefficient change. Let $x$ be a raw point of `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯` over $K$: a Weierstrass curve with unit discriminant together with $\Gamma_0$-power kernel polynomials indexed by the prime factors of $M'$, a level-$\ell$ datum, and a Drinfeld pair. The hypothesis `hx` summarises that $x$ is the Tate point at the cusp: the variable change $C_0$ over $\mathrm{LaurentSeries}\,L$ is normalised ($r=-1/12$, $s=-1/2$, $t=1/24$ and an identity pinning $u$ in terms of the Tate toric point at $![1,0]$), $x$'s curve becomes $C_0\cdot$`tateBase`$L(q\ell)$, its level-$\ell$ datum becomes the $C_0$-translate of `cuspData` at $![q,0]$, $![0,-q]$, its two Drinfeld sections pass through the affine coordinates of the $C_0$-translate of `cuspData` at $![\ell,0]$, $![0,-\ell]$, and the $j$-invariant of its class is `jqNModC`$L(q\ell)$. Let further $\gamma\in\Gamma_0(M')\subset \mathrm{SL}_2(\mathbb{Z})$, let $\tau$ be an $L$-algebra automorphism of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt`](def/ModularCurve_FullLevelLevelAutAt.html#L29) for $\gamma^{-1}$ (so that $\tau$ transforms quotients of integral $q$-expansions of forms of level $\Gamma_H$ according to the slash action by `conjElemN`$(q\ell)\,\gamma^{-1}$ under every complex embedding normalising $\xi$), let $\mu\in K^\times$ satisfy the explicit identity in $\mathrm{LaurentSeries}\,L$ relating the cusp points at $![1,0]$ and at $![\gamma_{00},-\gamma_{10}]$ modulo $q\ell$, and assume that scaling by $\langle\mu,0,0,0\rangle$ the $\tau$-transport of $x$ leaves the underlying curve unchanged. The conclusion asserts that the discriminant of the curve of $x$'s Drinfeld pair is a unit, and, with respect to that witness, that the Drinfeld-pair slot of $\langle\mu,0,0,0\rangle\cdot\tau_*x$ equals `RawDrinfeldPair.relabel` of $x$'s Drinfeld pair along the integral matrix $\gamma$, that is, the pair of sections $\gamma_{00}P+\gamma_{10}Q$ and $\gamma_{01}P+\gamma_{11}Q$ formed with the group law $\mathcal{G}$ on that curve.
--
--   This computes the effect on the $q$-level Drinfeld pair of the Galois-type automorphism attached to $\gamma\in\Gamma_0(M')$ at the Tate cusp, the identification of the automorphism with the matrix relabelling of the level structure. It feeds the assembly of the full-level moduli automorphism, [`ModularCurve.FullLevel.exists_variableChange_act_mapRing_eq_relabel_of_isLevelAutAt_of_level_fst_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_variableChange_act_mapRing_eq_relabel_of_isLevelAutAt_of_level_fst_gamma0Pow), where all three level slots are treated together.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_level_snd_snd_act_mapRing_eq_relabel_gamma0Pow.lean

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
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_level_snd_snd_act_mapRing_eq_relabel_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

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
    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K)
    (hx : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩

      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L (q * ℓ) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C₀ ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L (q * ℓ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1 + HahnSeries.C ((12 : L)⁻¹))))
    (hc : ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).curve = x.curve) :
    ∃ hΔ : IsUnit x.level.2.2.curve.Δ,
      ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.2 =
        ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ := by sorry
