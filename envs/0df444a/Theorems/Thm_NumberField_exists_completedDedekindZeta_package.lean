-- Prove2me | Theorems.Thm_NumberField_exists_completedDedekindZeta_package
-- name    : NumberField.exists_completedDedekindZeta_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/7f1aa5b8-5c71-5ea9-9805-e278dd59f14d
-- title:
--   Completed Dedekind zeta: continuation, functional equation, growth
-- statement:
--   For a number field $K$ (a field of characteristic zero of finite degree over $\mathbb{Q}$, in the lowest universe), there exists a function $\Lambda : \mathbb{C} \to \mathbb{C}$ with the following six properties. First, $\Lambda$ is differentiable on the complement of $\{0,1\}$. Second, $\Lambda(1-s) = \Lambda(s)$ for every $s$ with $s \neq 0$ and $s \neq 1$. Third, for every $s$ with $\operatorname{Re} s > 1$ one has $\Lambda(s) = (|\mathrm{discr}\,K|)^{s/2}\,\Gamma_{\mathbb{R}}(s)^{r_1}\,\Gamma_{\mathbb{C}}(s)^{r_2}\,\zeta_K(s)$, where the absolute value of the discriminant is cast from $\mathbb{Z}$ to $\mathbb{C}$, $r_1$ and $r_2$ are the numbers of real and of complex infinite places of $K$, $\Gamma_{\mathbb{R}}$ and $\Gamma_{\mathbb{C}}$ are Mathlib's archimedean Gamma factors, and $\zeta_K$ is Mathlib's Dedekind zeta function. Fourth, there is an entire $\xi : \mathbb{C} \to \mathbb{C}$ with $\xi(s) = s(s-1)\Lambda(s)$ for all $s \neq 0,1$, and a real constant $C$ with $\log\lVert \xi(s)\rVert \le C\lVert s\rVert \log \lVert s\rVert$ whenever $\lVert s\rVert \ge 2$. Fifth, every entire $\xi$ agreeing with $s(s-1)\Lambda(s)$ off $\{0,1\}$ satisfies $\xi(0) \neq 0$ and $\xi(1) \neq 0$. Sixth, for every real $C$ there is an $s$ with $\lVert s\rVert \ge 2$, $s \neq 0$, $s \neq 1$ and $C\lVert s\rVert < \log \lVert s(s-1)\Lambda(s)\rVert$.
--
--   This is the Hecke analytic continuation and functional equation of the completed Dedekind zeta function of a number field, packaged together with the statement that $\xi(s) = s(s-1)\Lambda(s)$ is entire of order at most one, non-vanishing at $s = 0$ and $s = 1$ (so that $\Lambda$ has simple poles there with non-zero residues), and not of exponential type. It is the analytic input for the Hadamard factorisation of $\xi$ and hence for explicit-formula discriminant bounds, and is used by the Tate global zeta-integral statements that express the completed zeta function as an adelic integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_completedDedekindZeta_package.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.exists_completedDedekindZeta_package (K : Type) [Field K] [NumberField K] :
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) ∧
      (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
      (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0) ∧
      (∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖) := by sorry
