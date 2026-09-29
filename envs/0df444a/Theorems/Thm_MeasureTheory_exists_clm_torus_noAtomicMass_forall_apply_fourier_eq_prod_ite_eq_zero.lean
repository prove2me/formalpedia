-- Prove2me | Theorems.Thm_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero
-- name    : MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/3208f6c3-29ad-5a72-94ca-10abdca0712e
-- title:
--   Haar functional on Tᵈ: box-small, Fourier values δ_{n,0}
-- statement:
--   Let $d$ be a natural number with $1 \le d$, and write $\mathbb{T} =$ `AddCircle (1 : ℝ)`, i.e. $\mathbb{R}/\mathbb{Z}$. The assertion is the existence of a continuous $\mathbb{C}$-linear functional $\mu$ on the space $C(\mathbb{T}^d, \mathbb{C})$ of continuous complex-valued functions on $\mathbb{T}^d$ (coordinates indexed by `Fin d`) with two properties. First, a smallness property on boxes: for every point $\tau \in \mathbb{T}^d$ and every real $\varepsilon > 0$ there are subsets $U_i \subseteq \mathbb{T}$, one for each coordinate $i$, each open and containing $\tau_i$, such that every continuous $g : \mathbb{T}^d \to \mathbb{C}$ which vanishes at every $\theta$ having some coordinate $\theta_i \notin U_i$ and satisfies $\|g(\theta)\| \le 1$ for all $\theta$ obeys $\|\mu(g)\| < \varepsilon$. Second, prescribed values on characters: for every $n : \mathrm{Fin}\, d \to \mathbb{Z}$ and every continuous $e$ with $e(\theta) = \prod_i \mathrm{fourier}(n_i)(\theta_i)$ for all $\theta$, one has $\mu(e) = \prod_{i} \bigl(\text{if } n_i = 0 \text{ then } 1 \text{ else } 0\bigr)$, an element of $\mathbb{C}$.
--
--   The functional in question is integration against the Haar probability measure of the $d$-dimensional torus, characterised by orthogonality of the characters $\theta \mapsto \prod_i e^{2\pi i n_i \theta_i}$; the first clause records that it gives arbitrarily small mass to suitable open boxes around any prescribed point, so that it carries no atom there. It is used in the construction of the functional appearing in [`AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add`](thm.html#AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add), where the continuous (non-atomic) part of a unipotent contribution is represented on a torus of Satake parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = ∏ i : Fin d, (if n i = 0 then (1 : ℂ) else 0) := by sorry
