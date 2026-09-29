-- Prove2me | Theorems.Thm_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange
-- name    : IsBaseChange.exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/0a4bf6de-356e-58bf-99d7-ea7aaabf1ec0
-- title:
--   Base change of a base change, compatibly with ψ
-- statement:
--   Let $R_0$ be a commutative ring, $R$ and $\Gamma_0$ commutative $R_0$-algebras, and $S$ a commutative ring that is simultaneously an $R_0$-algebra and an $R$-algebra, the two structures being compatible. Suppose given an $R_0$-algebra map $\psi\colon\Gamma_0\to S$ and an $R_0$-algebra isomorphism $\theta\colon\Gamma_0\otimes_{R_0}R\xrightarrow{\sim}S$ with $\theta(a\otimes 1)=\psi(a)$ for all $a\in\Gamma_0$ and $\theta(1\otimes r)=\mathrm{alg}_{R\to S}(r)$ for all $r\in R$. Let $L_0$ be an $R_0$-module, $L$ an $R$-module, and $e_L\colon R\otimes_{R_0}L_0\xrightarrow{\sim}L$ an $R$-linear isomorphism. Let $N_0$ be a $\Gamma_0$-module (compatibly an $R_0$-module) and $f_0\colon L_0\to N_0$ an $R_0$-linear map satisfying `IsBaseChange` over $\Gamma_0$, i.e. exhibiting $N_0$ as $\Gamma_0\otimes_{R_0}L_0$ through its universal property; likewise let $N$ be an $S$-module (compatibly an $R$-module) and $f\colon L\to N$ an $R$-linear map exhibiting $N$ as $S\otimes_R L$. Then there exists an $R$-linear isomorphism $\Phi\colon R\otimes_{R_0}N_0\xrightarrow{\sim}N$ such that (i) $\Phi(1\otimes f_0(x_0))=f(e_L(1\otimes x_0))$ for all $x_0\in L_0$; (ii) $\Phi(r\otimes\gamma\cdot n_0)=r\cdot\bigl(\psi(\gamma)\cdot\Phi(1\otimes n_0)\bigr)$ for all $r\in R$, $\gamma\in\Gamma_0$, $n_0\in N_0$; and (iii) for every $R$-module $N'$, two $R$-linear maps $g,g'\colon R\otimes_{R_0}N_0\to N'$ that agree on all elements $r\otimes(\gamma\cdot f_0(x_0))$ with $r\in R$, $\gamma\in\Gamma_0$, $x_0\in L_0$ are equal.
--
--   This is the transitivity of base change in the form needed to compare $R\otimes_{R_0}(\Gamma_0\otimes_{R_0}L_0)$ with $S\otimes_R L$ when $S=\Gamma_0\otimes_{R_0}R$, together with the fact that $N_0$ is generated over $\Gamma_0$ by the image of $f_0$, which yields the uniqueness clause (iii). It is used in the treatment of quasi-coherent modules on schemes obtained by base change, being cited by [`AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem IsBaseChange.exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange
    {R₀ : Type u} [CommRing R₀] {R : Type u} [CommRing R] [Algebra R₀ R]
    {Γ₀ : Type u} [CommRing Γ₀] [Algebra R₀ Γ₀]
    {S : Type u} [CommRing S] [Algebra R₀ S] [Algebra R S] [IsScalarTower R₀ R S]
    (ψ : Γ₀ →ₐ[R₀] S) (θ : Γ₀ ⊗[R₀] R ≃ₐ[R₀] S)
    (hθ₁ : ∀ a : Γ₀, θ (a ⊗ₜ (1 : R)) = ψ a) (hθ₂ : ∀ r : R, θ ((1 : Γ₀) ⊗ₜ r) = algebraMap R S r)
    {L₀ : Type v} [AddCommGroup L₀] [Module R₀ L₀]
    {L : Type v} [AddCommGroup L] [Module R L] (eL : R ⊗[R₀] L₀ ≃ₗ[R] L)
    {N₀ : Type w} [AddCommGroup N₀] [Module R₀ N₀] [Module Γ₀ N₀] [IsScalarTower R₀ Γ₀ N₀]
    (f₀ : L₀ →ₗ[R₀] N₀) (hf₀ : IsBaseChange Γ₀ f₀)
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : L →ₗ[R] N) (hf : IsBaseChange S f) :
    ∃ Φ : R ⊗[R₀] N₀ ≃ₗ[R] N,
      (∀ x₀ : L₀, Φ ((1 : R) ⊗ₜ f₀ x₀) = f (eL ((1 : R) ⊗ₜ x₀))) ∧
      (∀ (r : R) (γ : Γ₀) (n₀ : N₀), Φ (r ⊗ₜ (γ • n₀)) = r • (ψ γ • Φ ((1 : R) ⊗ₜ n₀))) ∧
      (∀ (N' : Type w) [AddCommGroup N'] [Module R N'] (g g' : R ⊗[R₀] N₀ →ₗ[R] N'),
          (∀ (r : R) (γ : Γ₀) (x₀ : L₀), g (r ⊗ₜ (γ • f₀ x₀)) = g' (r ⊗ₜ (γ • f₀ x₀))) → g = g') := by sorry
