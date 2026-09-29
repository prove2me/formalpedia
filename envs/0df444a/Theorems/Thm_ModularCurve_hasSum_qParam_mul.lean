-- Prove2me | Theorems.Thm_ModularCurve_hasSum_qParam_mul
-- name    : ModularCurve.hasSum_qParam_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/80018164-7c58-5a39-86ee-244003282ffa
-- title:
--   Products of convergent q-expansions on H
-- statement:
--   Let $h$ be a real number with $0 < h$, let $A, B \in \mathbb{C}[[q]]$ be formal power series over $\mathbb{C}$, and let $F, G \colon \mathfrak{H} \to \mathbb{C}$ be arbitrary functions on the upper half-plane. Assume that for every $\tau \in \mathfrak{H}$ the family $m \mapsto a_m\, \mathbf{q}_h(\tau)^m$, indexed by $m \in \mathbb{N}$, where $a_m$ is the $m$-th coefficient of $A$ and $\mathbf{q}_h(\tau) = \exp(2\pi i \tau / h)$ is Mathlib's `Function.Periodic.qParam h (τ : ℂ)`, is summable with sum $F(\tau)$; and likewise that for every $\tau \in \mathfrak{H}$ the family $m \mapsto b_m\, \mathbf{q}_h(\tau)^m$ built from the coefficients of $B$ is summable with sum $G(\tau)$. Then for each $\tau \in \mathfrak{H}$ the family $m \mapsto c_m\, \mathbf{q}_h(\tau)^m$, where $c_m = \sum_{i+j=m} a_i b_j$ is the $m$-th coefficient of the product power series $A \cdot B$, is summable with sum $F(\tau) G(\tau)$. Note that the hypotheses are required at every point of $\mathfrak H$, while the conclusion is asserted at the single given point $\tau$.
--
--   This is the statement that functions realised on the upper half-plane by convergent $q$-expansions at a fixed period $h$ are closed under multiplication, with the Cauchy product of the coefficient series computing the product function. It underlies the construction of integral $q$-expansions of Siegel units and of the associated modular forms for $\Gamma_1(N)$, which invoke it when multiplying $q$-expansions and taking powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_qParam_mul.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.PowerSeries.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_qParam_mul (h : ℝ) (hh : 0 < h) (A B : PowerSeries ℂ) (F G : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m A * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m B * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℕ => PowerSeries.coeff m (A * B) * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ * G τ) := by sorry
