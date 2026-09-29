-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/380b75c7-0231-590b-93be-34136b08db11
-- title:
--   Uniqueness, composition and triviality of guarded level automorphisms
-- statement:
--   Let $q$ be a prime, let $M'\ge 1$ with $q \nmid M'$, and let $\ell_g \mid M'$. Let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of reduction $(\mathbb{Z}/q^2M')^{\times}\to(\mathbb{Z}/q)^{\times}$, with the kernel of reduction $(\mathbb{Z}/q^2M')^{\times}\to(\mathbb{Z}/\ell_g)^{\times}$. Let $L$ be a field of characteristic $0$ containing a primitive $q$-th root of unity $\xi$, and assume there is a ring homomorphism $L\to\mathbb{C}$ sending $\xi$ to $e^{2\pi i/q}$. Let $K$ be the intermediate field of $L(\!(T)\!)$ generated over $L$ by the coefficientwise image of the $q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') H₁`](def/ModularCurve_XH.html#L79) of $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$. For $\gamma\in SL_2(\mathbb{Z})$ and $\tau$ an $L$-automorphism of $K$, the relation `IsLevelAutAt` says: for every weight $k$, all weight-$k$ forms $f,g$ on $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f,p_g$, $p_g\neq 0$, every $x\in K$ whose Laurent series is $p_f/p_g$, and every embedding $\iota:L\to\mathbb{C}$ with $\iota(\xi)=e^{2\pi i/q}$, one has $\iota(\tau x)\cdot q\text{-exp}(g\mid_k \gamma^{\sharp}) = q\text{-exp}(f\mid_k\gamma^{\sharp})$, where $\gamma^{\sharp}=\mathrm{diag}(q,1)^{-1}\gamma\,\mathrm{diag}(q,1)$. The conclusion is threefold: for $\gamma\in\Gamma_0(M')$ at most one $\tau$ satisfies the relation at $\gamma$; if $\tau$ satisfies it at $\gamma\in\Gamma_0(M')$ and $\sigma$ at $\delta\in\Gamma_0(M')$, then $\tau\sigma$ satisfies it at $\delta\gamma$; and if $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ with $\gamma_{11}\equiv 1 \pmod{\ell_g}$, then the identity automorphism satisfies it at $\gamma$.
--
--   This is the basic well-definedness package for the Galois action of $\Gamma_0(M')$ on the $\Gamma_{H_1}(q^2M')$-level $q$-expansion field: uniqueness of the automorphism attached to $\gamma$, the anti-multiplicative composition law, and triviality on the subgroup $\Gamma(q)\cap\Gamma_0(M')$ cut out further by $d_\gamma\equiv1 \pmod{\ell_g}$. It underlies the constructions of the level automorphism group acting on models and blow-up charts of the modular curve at full level, and is invoked throughout that development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ τ' : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K τ →
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K τ' →
      τ = τ') ∧

    (∀ γ δ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → δ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ σ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K τ →
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ δ K σ →
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ (δ * γ) K (τ * σ)) ∧

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
      ((γ 1 1 : ℤ) : ZMod ℓg) = 1 →
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K 1) := by sorry
