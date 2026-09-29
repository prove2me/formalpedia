-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le
-- name    : MeasureTheory.exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/b0a49a77-d4c4-5a40-a10c-54a4205024ec
-- title:
--   Uniform lattice-sum bound for a skew product Poisson kernel
-- statement:
--   Fix natural numbers $a$, $b$, $r$ and a continuous $\mathbb{R}$-linear isomorphism $S : (\mathbb{R}^a \times \mathbb{R}^b) \xrightarrow{\ \sim\ } \mathbb{R}^r$, where $\mathbb{R}^a$, $\mathbb{R}^b$, $\mathbb{R}^r$ denote the spaces of functions on `Fin a`, `Fin b`, `Fin r` with their usual topologies. The assertion is that there exists a real constant $K$, depending only on $a$, $b$, $r$ and $S$, such that for every $\psi \in \mathbb{R}^a$ and every $t \in \mathbb{R}^r$ the following three statements hold for the kernel $$F_{\kappa}(\eta) \;=\; \prod_{i \in \mathrm{Fin}\,r} \bigl(1 + \lvert S(\kappa + \psi,\, \eta)_i - t_i \rvert\bigr)^{-2},$$ in which $\kappa \in \mathbb{Z}^a$ is shifted by $\psi$ coordinatewise after inclusion $\mathbb{Z} \hookrightarrow \mathbb{R}$: first, for each $\kappa \in \mathbb{Z}^a$ the function $\eta \mapsto F_\kappa(\eta)$ is integrable on $\mathbb{R}^b$ for the volume measure; second, the family $\kappa \mapsto \int_{\mathbb{R}^b} F_\kappa(\eta)\, d\eta$ is summable over $\mathbb{Z}^a$; and third, $\sum_{\kappa \in \mathbb{Z}^a} \int_{\mathbb{R}^b} F_\kappa(\eta)\, d\eta \le K$. The point is the order of quantifiers: the bound $K$ is uniform in the shift $\psi$ and in the recentring $t$.
--
--   This is a Riemann-sum comparison: the sum over the sheets $\kappa + \psi$ of a skewed lattice of the fibre integrals of the product kernel $\prod_i (1+|\xi_i|)^{-2}$ is bounded independently of the shift and of the translation of the kernel. It serves as the quantitative input for a Poisson-summation-type estimate, where it yields a bound, uniform in the character and in the window used, for the total mass of a sum of fibrewise Fourier contributions over a discrete subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le
    (a b r : ℕ) (S : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] (Fin r → ℝ)) :
    ∃ K : ℝ, ∀ (ψ : Fin a → ℝ) (t : Fin r → ℝ),
      (∀ κ : Fin a → ℤ, Integrable fun η : Fin b → ℝ =>
        ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2) ∧
      Summable (fun κ : Fin a → ℤ =>
        ∫ η : Fin b → ℝ, ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2) ∧
      ∑' κ : Fin a → ℤ, ∫ η : Fin b → ℝ, ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2 ≤ K := by sorry
