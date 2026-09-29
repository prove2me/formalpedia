-- Prove2me | Theorems.Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq
-- name    : ModularForm.exists_rankinCohen_one_qExpansion_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e8850798-0c57-5fb7-a64a-92cd6acf63fa
-- title:
--   First Rankin–Cohen bracket of modular forms
-- statement:
--   Let $\Gamma$ be a subgroup of finite index of $\mathrm{SL}_2(\mathbb{Z})$ such that the real number $1$ is a strict period of the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, i.e. $1$ lies in `strictPeriods` of that image, so that translation by $1$ is available and $q = e^{2\pi i \tau}$ is the correct local parameter at $\infty$. Let $k_1, k_2$ be integers, let $g$ be a modular form on $\Gamma$ of weight $k_1$ and $h$ a modular form on $\Gamma$ of weight $k_2$. The assertion is that there exists a modular form $B$ on $\Gamma$ of weight $k_1 + k_2 + 2$ with two properties. First, for every $\tau$ in the upper half-plane, $B(\tau) = k_1\, g(\tau)\, (Dh)(\tau) - k_2\, (Dg)(\tau)\, h(\tau)$, where $D$ denotes `Derivative.normalizedDerivOfComplex`, the normalised derivative $(2\pi i)^{-1}\, d/d\tau = q\, d/dq$. Second, the $q$-expansion of $B$ with respect to the period $1$ equals, as a power series over $\mathbb{C}$, $$k_1 \cdot \tilde g \cdot \vartheta\tilde h - k_2 \cdot (\vartheta \tilde g) \cdot \tilde h,$$ where $\tilde g, \tilde h$ are the $q$-expansions of $g$ and $h$ for the period $1$, the constants $k_1, k_2$ enter as the constant power series `PowerSeries.C` of their images in $\mathbb{C}$, and $\vartheta$ is the operator sending a power series with coefficients $a_n$ to the series with coefficients $n\,a_n$.
--
--   This is the first Rankin–Cohen bracket $[g,h]_1 = k_1 g\,Dh - k_2\,(Dg)h$: the non-modular terms in the derivatives of $g$ and $h$ cancel in this combination, so the bracket is again a modular form, of weight raised by $2$, and its $q$-expansion is given by the coefficientwise operator $\vartheta = q\,d/dq$. It serves in the project as the source of weight-raising operations on $q$-expansions, and is used in the construction of differentials attached to cusp forms with integral $q$-expansions and in the study of mod $p$ modular forms and of the diamond operators on $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_rankinCohen_one_qExpansion_eq
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    {k₁ k₂ : ℤ} (g : ModularForm Γ k₁) (h : ModularForm Γ k₂) :
    ∃ B : ModularForm Γ (k₁ + k₂ + 2),
      (∀ τ : ℍ, B τ = k₁ * g τ * Derivative.normalizedDerivOfComplex h τ
                     - k₂ * Derivative.normalizedDerivOfComplex g τ * h τ) ∧
      qExpansion 1 (B : ℍ → ℂ) =
        PowerSeries.C (k₁ : ℂ) * qExpansion 1 (g : ℍ → ℂ) *
            PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (h : ℍ → ℂ)).coeff n)
          - PowerSeries.C (k₂ : ℂ) *
            PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (g : ℍ → ℂ)).coeff n) *
              qExpansion 1 (h : ℍ → ℂ) := by sorry
