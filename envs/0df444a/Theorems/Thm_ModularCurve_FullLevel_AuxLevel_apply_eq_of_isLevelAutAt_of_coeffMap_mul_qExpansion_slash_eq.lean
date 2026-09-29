-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
-- name    : ModularCurve.FullLevel.AuxLevel.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/e5636523-3b7c-5a28-b827-bf5794431cfd
-- title:
--   Level automorphism determined on ratios of modular forms
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'\ge 1$ with $q\nmid M'$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell)$-th root of unity $\xi$, and let $\iota:L\to\mathbb{C}$ be a ring homomorphism with $\iota(\xi)=\exp(2\pi i/(q\ell))$. Put $N_0=(q\ell)^2M'$ and let $H=\mathrm{levelH}$ be the kernel of the reduction $(\mathbb{Z}/N_0)^\times\to(\mathbb{Z}/q\ell)^\times$; let $K$ be the intermediate field of $L((X))$ obtained by adjoining to $L$ the image, under coefficientwise extension of scalars $\mathbb{Q}\to L$, of the $q$-expansion function field $\mathrm{xHFunctionField}\,N_0\,H$. Let $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying $\mathrm{IsLevelAutAt}$ for the data $(q\ell,\xi,q\ell,N_0,H,\gamma^{-1})$: for every weight $k$, every pair $f,g$ of weight-$k$ modular forms for $\mathrm{GammaH}\,N_0\,H$ whose $q$-expansions of width $1$ come from integral power series $p_f,p_g$ with the Laurent series attached to $p_g$ nonzero, every $x\in K$ whose underlying Laurent series is the image of the quotient of those Laurent series, and every $\iota'$ with $\iota'(\xi)=\exp(2\pi i/(q\ell))$, one has $\iota'_*(\tau x)\cdot q\text{-exp}(g\mid_k\mathrm{conjElemN}(q\ell,\gamma^{-1}))=q\text{-exp}(f\mid_k\mathrm{conjElemN}(q\ell,\gamma^{-1}))$, where $\mathrm{conjElemN}(m,\delta)=\begin{pmatrix}\delta_{00}&\delta_{01}/m\\ m\delta_{10}&\delta_{11}\end{pmatrix}\in\mathrm{GL}_2(\mathbb{R})$. Then, for all $X,Y\in K$, all $k\in\mathbb{Z}$ and all weight-$k$ modular forms $F,G$ for $\mathrm{GammaH}\,N_0\,H$ with $G\ne 0$ such that $\iota_*X\cdot q\text{-exp}(G)=q\text{-exp}(F)$ and $\iota_*Y\cdot q\text{-exp}(G\mid_k\mathrm{conjElemN}(q\ell,\gamma^{-1}))=q\text{-exp}(F\mid_k\mathrm{conjElemN}(q\ell,\gamma^{-1}))$, one has $\tau X=Y$.
--
--   This identifies the action of a level automorphism attached to $\gamma^{-1}$ on any element of the function field of $X_H$ presented as a ratio $F/G$ of weight-$k$ modular forms: its image is the corresponding ratio of the slashed forms $F\mid_k\gamma^{-1}$ and $G\mid_k\gamma^{-1}$, the hypothesis $\mathrm{IsLevelAutAt}$ being assumed only for ratios of integral $q$-expansions. It is used in the description of how these automorphisms permute the torsion coordinate functions, and hence in the identification of the Galois action on the relevant curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.AuxLevel.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
    (X Y : ↥K) (k : ℤ)
    (F G : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
      Subgroup (GL (Fin 2) ℝ)) k)
    (hG : G ≠ 0)
    (hX : ModularCurve.coeffMap ι ((X : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑G)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑F)))
    (hY : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      ModularCurve.coeffMap ι ((Y : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
          (⇑G ∣[k] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
          (⇑F ∣[k] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹))) :
    τ X = Y := by sorry
