-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
-- name    : ModularCurve.FullLevel.Diamond.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/faee83e7-df32-5c89-aae6-5521fae61e24
-- title:
--   Level automorphism determined by q-expansion form ratios
-- statement:
--   Fix a prime $q$, an $M'\ge 1$ with $q\nmid M'$, and a prime $\ell_g$ with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $q\ell_g$-th root of unity, and $\iota:L\to\mathbb C$ a ring map with $\iota(\xi)=e^{2\pi i/(q\ell_g)}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernels of reduction to $(\mathbb Z/q)^\times$ and to $(\mathbb Z/\ell_g)^\times$, and let $K\subseteq L((\mathsf q))$ be the intermediate field generated over $L$ by the image, under coefficientwise extension of scalars, of the rational function field `xHFunctionField` of level $q^2M'$ and character group $H_1$. Let $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lie in $\Gamma_0(M')$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for the data $(q,\xi^{\ell_g},q,q^2M',H_1,\gamma^{-1})$: for all weights $k$, all weight-$k$ modular forms $f,g$ on $\Gamma_{H_1}(q^2M')$ (the subgroup of $\Gamma_0(q^2M')$ whose lower-right entry mod $q^2M'$ lies in $H_1$, viewed in $\mathrm{GL}_2(\mathbb R)$) with integral $q$-expansions $p_f,p_g$, $p_g$ having nonzero image over $\mathbb Q$, all $x\in K$ equal to the coefficientwise image of $p_f/p_g$, and all $\iota':L\to\mathbb C$ with $\iota'(\xi^{\ell_g})=e^{2\pi i/q}$, one has $\iota'(\tau x)\cdot\widehat{q}\big(g\mid_k \gamma^{-1\sharp}\big)=\widehat q\big(f\mid_k\gamma^{-1\sharp}\big)$, where $\delta^{\sharp}=\mathrm{diag}(q,1)^{-1}\delta\,\mathrm{diag}(q,1)$ and $\widehat q$ denotes the width-one $q$-expansion in $\mathbb C((\mathsf q))$. Then for $X,Y\in K$, $k\in\mathbb Z$ and weight-$k$ modular forms $F,G$ on $\Gamma_{H_1}(q^2M')$ with $G\ne0$, the two identities $\iota(X)\,\widehat q(G)=\widehat q(F)$ and $\iota(Y)\,\widehat q(G\mid_k\gamma^{-1\sharp})=\widehat q(F\mid_k\gamma^{-1\sharp})$ force $\tau X=Y$.
--
--   This identifies the level automorphism attached to $\gamma^{-1}$ on the $H_1$-level modular function field as pull-back along $\gamma^{-1\sharp}$ on every element admitting a representation as a ratio of two modular forms of equal weight, extending the defining property from ratios of integral $q$-expansions to arbitrary form ratios. It is used in the computation of the diamond action on Tate and cusp points, and in the identification of level automorphisms with units acting on the relevant rigid data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.Diamond.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ)
    (X Y : ↥K) (k : ℤ)
    (F G : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) k)
    (hG : G ≠ 0)
    (hX : ModularCurve.coeffMap ι ((X : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑G)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑F)))
    (hY : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ModularCurve.coeffMap ι ((Y : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
          (⇑G ∣[k] ModularCurve.FullLevel.conjElemN q γ⁻¹)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
          (⇑F ∣[k] ModularCurve.FullLevel.conjElemN q γ⁻¹))) :
    τ X = Y := by sorry
