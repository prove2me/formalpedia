-- Prove2me | Theorems.Thm_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even
-- name    : ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d9ec72f8-2d18-5965-90e4-1b491d9bd1e4
-- title:
--   Galois transport of K-rational modular forms on Γ₁(N), even weight
-- statement:
--   Let $N$ be a positive natural number, let $k$ be an integer which is even, and let $K$ be an intermediate field of $\mathbb{C}/\mathbb{Q}$ which is assumed to equal the subfield $\mathbb{Q}(\exp(2\pi i/N))$ generated over $\mathbb{Q}$ by the single element $\exp(2\pi i/N)$. Let $\sigma : K \to K$ be a $\mathbb{Q}$-algebra automorphism of $K$. Let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_1(N)$, and let $c : \mathbb{N} \to K$ be a sequence of elements of $K$ such that for every $m$ the $m$-th coefficient of the $q$-expansion of $f$ of period $1$ — that is, `ModularForm.qCoeff f m`, the $m$-th coefficient of `qExpansion 1 f` — equals the image of $c\,m$ in $\mathbb{C}$. The conclusion asserts the existence of a modular form $f'$ of the same weight $k$ for $\Gamma_1(N)$ all of whose $q$-expansion coefficients of period $1$ are the images in $\mathbb{C}$ of the elements $\sigma(c\,m)$, i.e. $\sum_m \sigma(c_m) q^m$ is again the expansion of a modular form on $\Gamma_1(N)$ of weight $k$.
--
--   This is the rationality-and-Galois-equivariance statement for holomorphic modular forms on $\Gamma_1(N)$ with Fourier coefficients in the cyclotomic field $\mathbb{Q}(\zeta_N)$: the space of such forms is stable under the action of $\mathrm{Gal}(\mathbb{Q}(\zeta_N)/\mathbb{Q})$ on $q$-expansion coefficients, in the even-weight case. It is the modular-form counterpart of the corresponding statement for cusp forms, and feeds the companion result [`ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply`](thm.html#ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply), where the parity restriction on $k$ is removed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even (N : ℕ) [NeZero N] (k : ℤ)
    (hk : Even k) (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (σ : ↥K ≃ₐ[ℚ] ↥K) (f : ModularForm (CongruenceSubgroup.Gamma1 N) k) (c : ℕ → ↥K)
    (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    ∃ f' : ModularForm (CongruenceSubgroup.Gamma1 N) k,
      ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := by sorry
