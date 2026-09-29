-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
-- name    : ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/71831422-3c59-57ef-8f2e-6f0d9124a06d
-- title:
--   Forms on Γ_{H_1}(q²M') realising toric Tate-point coordinates
-- statement:
--   Let $q$ be a prime, $M'\ge 1$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $q\ell_g$-th root of unity, and $\iota:L\to\mathbb C$ a ring homomorphism with $\iota(\xi)=\exp(2\pi i/(q\ell_g))$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb Z/q)^\times$ with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$. Write $\Gamma_{H_1}$ for the subgroup of $SL(2,\mathbb Z)$ consisting of the matrices in $\Gamma_0(q^2M')$ whose lower-right entry reduces into $H_1$, viewed inside $GL(2,\mathbb R)$. Then there are families $A^t,B^t,R^t$ of modular forms on $\Gamma_{H_1}$, indexed by $L^\times$, of weights $6$, $4$ and $3$ respectively, such that for every $c\in L^\times$ with $c^{\ell_g}=1$ and $c\ne 1$, writing $(x_c,y_c)$ for the pair of Laurent series over $L$ given by the explicit divisor-sum power series of [`ModularCurve.tateToricPoint L q c`](def/ModularCurve_KatzLevelPCusps.html#L20) (the coordinates of the toric point attached to $c$ on the Tate curve with level parameter $q$), and $\hat q(\cdot)$ for the width-$1$ $q$-expansion regarded as an element of $\mathbb C((\mathsf q))$: $\hat q(B^t_c)\ne 0$; $\hat q(B^t_c)$ is the coefficientwise image under $\iota$ of some Laurent series over $L$; $\iota_*(x_c+1/12)\cdot\hat q(B^t_c)=\hat q(A^t_c)$; and $\hat q(R^t_c)=\iota_*(2y_c+x_c)$. Moreover, for every $\rho\in SL(2,\mathbb Z)$ lying in $\Gamma_0(M')$ and every such $c$, slashing by the determinant-one real matrix $\bigl(\begin{smallmatrix}\rho_{00}&\rho_{01}/q\\ q\rho_{10}&\rho_{11}\end{smallmatrix}\bigr)$ in the respective weights sends $A^t_c,B^t_c,R^t_c$ to $A^t_{c^{\rho_{11}}},B^t_{c^{\rho_{11}}},R^t_{c^{\rho_{11}}}$.
--
--   This supplies the weight $6$, $4$ and $3$ families on $\Gamma_{H_1}(q^2M')$ whose $q$-expansions express, over the image of $\iota$, the affine coordinates of the toric $\ell_g$-torsion points of the Tate curve, together with the diamond law $c\mapsto c^{\rho_{11}}$ for the conjugates $\mathrm{diag}(1,q)\rho\,\mathrm{diag}(1,q)^{-1}$ of elements $\rho\in\Gamma_0(M')$. It is used in the study of the level automorphisms attached to this full-level rigid data, in particular in the lemmas identifying the action on cusp points and on toric points up to a unit factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq.lean

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

theorem ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ (At : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 6)
      (Bt : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (Rt : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 3),
      (∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) ≠ 0 ∧
        (∃ b : LaurentSeries L, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) = ModularCurve.coeffMap ι b) ∧
        ModularCurve.coeffMap ι ((ModularCurve.tateToricPoint L q c).1 + HahnSeries.C ((12 : L)⁻¹)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(At c))) ∧
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rt c))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.tateToricPoint L q c).2 + (ModularCurve.tateToricPoint L q c).1)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' → ∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        (⇑(At c) ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(At (c ^ ((ρ 1 1 : ℤ)))) ∧
        (⇑(Bt c) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Bt (c ^ ((ρ 1 1 : ℤ)))) ∧
        (⇑(Rt c) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Rt (c ^ ((ρ 1 1 : ℤ))))) := by sorry
