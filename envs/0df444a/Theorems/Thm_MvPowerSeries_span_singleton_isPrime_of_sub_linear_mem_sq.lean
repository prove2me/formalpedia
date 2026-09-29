-- Prove2me | Theorems.Thm_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq
-- name    : MvPowerSeries.span_singleton_isPrime_of_sub_linear_mem_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/5b4d70b1-b73e-57a0-adb0-86ff80ab7a7c
-- title:
--   Power series with non-zero linear part: prime ideal and tangent line
-- statement:
--   Let $\kappa$ be a field and let $a, b \in \kappa$ with $a \neq 0$ or $b \neq 0$. Let $\ell$ be a formal power series in two variables $X_0, X_1$ over $\kappa$ (indexed by `Fin 2`) whose difference $\ell - (aX_0 + bX_1)$ lies in the square of the ideal $\mathfrak m = (X_0, X_1)$, i.e. $\ell$ has linear part $aX_0 + bX_1$ and zero constant term. The conclusion is a conjunction of four assertions: (1) the principal ideal $(\ell)$ is prime; (2) $X_0 \notin (\ell)$ or $X_1 \notin (\ell)$; (3) every prime ideal $P$ of $\kappa[[X_0, X_1]]$ containing $\ell$ and not containing both $X_0$ and $X_1$ is equal to $(\ell)$; and (4) for all $a', b' \in \kappa$ and every $h' \in \mathfrak m^2$, if $a'X_0 + b'X_1 + h' \in (\ell)$ then $ab' - a'b = 0$, so that any element of $(\ell)$ has linear part proportional to $aX_0 + bX_1$.
--
--   This is the local statement that a two-variable power series with non-zero linear part cuts out a smooth branch: its ideal is prime, is the unique prime containing it apart from the maximal ideal, and determines its tangent direction. It serves as the algebraic input for the local analysis of branches through a point on the Drinfeld curve, being used there to identify the branch primes, to show the corresponding quotients are discrete valuation rings, and to prove a radicality statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open MvPowerSeries

theorem MvPowerSeries.span_singleton_isPrime_of_sub_linear_mem_sq
    {κ : Type u} [Field κ] (a b : κ) (hab : a ≠ 0 ∨ b ≠ 0)
    (ℓ : MvPowerSeries (Fin 2) κ)
    (hℓ : ℓ - (C a * X 0 + C b * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2) :
    (Ideal.span {ℓ}).IsPrime ∧
    ((X 0 : MvPowerSeries (Fin 2) κ) ∉ Ideal.span {ℓ} ∨ (X 1 : MvPowerSeries (Fin 2) κ) ∉ Ideal.span {ℓ}) ∧
    (∀ P : Ideal (MvPowerSeries (Fin 2) κ), P.IsPrime → ℓ ∈ P →
      ((X 0 : MvPowerSeries (Fin 2) κ) ∉ P ∨ (X 1 : MvPowerSeries (Fin 2) κ) ∉ P) → P = Ideal.span {ℓ}) ∧
    (∀ (a' b' : κ) (h' : MvPowerSeries (Fin 2) κ),
      h' ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 →
      C a' * X 0 + C b' * X 1 + h' ∈ Ideal.span {ℓ} → a * b' - a' * b = 0) := by sorry
