-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one
-- name    : LanglandsTunnell.RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/d6ba7e53-f01c-5302-8674-d4c5476e4add
-- title:
--   Two-row Cauchy identity inverting the GL₂timesGL₃ Euler polynomial
-- statement:
--   Let $R$ be a commutative ring and let $a,b,e_1,e_2,e_3 \in R$. Let $t : \mathbb{N} \to R$ satisfy $t_0 = 1$, $t_1 = a$ and $t_{m+2} = a\,t_{m+1} - b\,t_m$ for all $m$, and let $h : \mathbb{N} \to R$ satisfy $h_0 = 1$, $h_1 = e_1$, $h_2 = e_1^2 - e_2$ and $h_{n+3} = e_1 h_{n+2} - e_2 h_{n+1} + e_3 h_n$ for all $n$. Let $u : \mathbb{N} \to \mathbb{N} \to R$ satisfy $u_{k,0} = h_k$ for all $k$ and $u_{k_1,k_2+1} = h_{k_1} h_{k_2+1} - h_{k_1+1} h_{k_2}$ for all $k_1,k_2$. Then the power series over $R$ whose $n$-th coefficient is $\sum_{k_2=0}^{\lfloor n/2 \rfloor} b^{k_2}\, t_{n-2k_2}\, u_{\,n-k_2,\;k_2}$, multiplied by the image in $R[[X]]$ of the polynomial $$1 - a e_1 X + (a^2 e_2 + b e_1^2 - 2 b e_2) X^2 + (-a^3 e_3 - a b e_1 e_2 + 3 a b e_3) X^3 + (a^2 b e_1 e_3 - 2 b^2 e_1 e_3 + b^2 e_2^2) X^4 - a b^2 e_2 e_3 X^5 + b^3 e_3^2 X^6,$$ equals $1$.
--
--   This is Cauchy's identity $\sum_\lambda s_\lambda(\alpha) s_\lambda(\beta) X^{|\lambda|} = \prod_{i,j} (1 - \alpha_i \beta_j X)^{-1}$ restricted to partitions $\lambda$ with at most two rows, expressed purely in terms of the coefficients $a,b$ of a quadratic and $e_1,e_2,e_3$ of a cubic, with the right-hand side realised as the degree-six Rankin–Selberg Euler polynomial `rsEulerPoly`. It supplies the formal inversion of the local $\mathrm{GL}_2 \times \mathrm{GL}_3$ Euler factor used in the cubic-induction step, being cited in the construction of normalised new vectors from local Whittaker data and in the identification of spherical torus values of induced coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.RingTheory.PowerSeries.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one
    {R : Type*} [CommRing R] (a b e₁ e₂ e₃ : R)
    (t : ℕ → R) (ht0 : t 0 = 1) (ht1 : t 1 = a) (ht : ∀ m : ℕ, t (m + 2) = a * t (m + 1) - b * t m)
    (h : ℕ → R) (hh0 : h 0 = 1) (hh1 : h 1 = e₁) (hh2 : h 2 = e₁ ^ 2 - e₂)
    (hh : ∀ n : ℕ, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n)
    (u : ℕ → ℕ → R) (hu0 : ∀ k : ℕ, u k 0 = h k)
    (hu : ∀ k₁ k₂ : ℕ, u k₁ (k₂ + 1) = h k₁ * h (k₂ + 1) - h (k₁ + 1) * h k₂) :
    PowerSeries.mk (fun n : ℕ => ∑ k₂ ∈ Finset.range (n / 2 + 1), b ^ k₂ * t (n - 2 * k₂) * u (n - k₂) k₂) *
        ↑(rsEulerPoly a b e₁ e₂ e₃) = (1 : PowerSeries R) := by sorry
