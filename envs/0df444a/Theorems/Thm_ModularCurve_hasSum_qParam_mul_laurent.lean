-- Prove2me | Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
-- name    : ModularCurve.hasSum_qParam_mul_laurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/5ca5ba5d-c794-56a8-8914-c255b7154dab
-- title:
--   Cauchy product of Laurent q-expansions on H
-- statement:
--   Let $h$ be a real number with $0 < h$, let $A, B \in \mathbb{C}(\!(q)\!)$ be formal Laurent series over $\mathbb{C}$ (elements of `LaurentSeries ℂ`, i.e. Hahn series indexed by $\mathbb{Z}$), and let $F, G \colon \mathfrak H \to \mathbb{C}$ be arbitrary functions on the upper half-plane. Assume that for every $\tau \in \mathfrak H$ the family $m \mapsto A_m\, q_h(\tau)^m$, indexed by $m \in \mathbb{Z}$, is summable with sum $F(\tau)$, where $A_m$ denotes the coefficient of $A$ in degree $m$, $q_h(\tau) = \exp(2\pi i \tau / h)$ is the Mathlib nome `Function.Periodic.qParam h (τ : ℂ)`, and the power is an integer power; assume likewise that for every $\tau$ the family $m \mapsto B_m\, q_h(\tau)^m$ is summable with sum $G(\tau)$. Then for any prescribed $\tau \in \mathfrak H$ the family $m \mapsto (AB)_m\, q_h(\tau)^m$, $m \in \mathbb{Z}$, is summable with sum $F(\tau)\,G(\tau)$, the coefficients $(AB)_m$ being those of the product of $A$ and $B$ in the ring of formal Laurent series. Summability is unconditional summability of a family (`HasSum`), not convergence of a symmetric partial-sum limit.
--
--   This is the Cauchy-product rule for $q$-expansions in the Laurent (meromorphic-at-the-cusp) setting, as needed for modular functions such as $j = q^{-1} + 744 + \cdots$ whose expansions have a pole at $\infty$. It is used throughout the project whenever a product of two functions given by convergent Laurent $q$-expansions is identified with the $q$-expansion of the product series, for instance in the work with hyperplane sections and coset polynomials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_qParam_mul_laurent.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_qParam_mul_laurent (h : ℝ) (hh : 0 < h) (A B : LaurentSeries ℂ) (F G : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => B.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (A * B).coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ * G τ) := by sorry
