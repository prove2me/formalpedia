-- Prove2me | Theorems.Thm_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow
-- name    : MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/2763b927-3aca-5bea-af67-b447fda031c6
-- title:
--   Atom-free functional on Tᵈ with prescribed Fourier values
-- statement:
--   Let $d \in \mathbb{N}$ with $2 \le d$, let $p$ be an index in $\mathrm{Fin}\,d$, and let $q \in \mathbb{N}$. Writing $\mathbb{T} =$ `AddCircle (1 : ℝ)` $= \mathbb{R}/\mathbb{Z}$, the assertion is that there exists a continuous $\mathbb{C}$-linear functional $\mu$ on the space $C(\mathbb{T}^d, \mathbb{C})$ of continuous complex-valued functions on the $d$-torus with the following two properties. First, a box smallness (absence of atomic mass) property: for every point $\tau \in \mathbb{T}^d$ and every real $\varepsilon > 0$ there are sets $U_i \subseteq \mathbb{T}$, one for each coordinate $i$, with each $U_i$ open and containing $\tau_i$, such that every $g \in C(\mathbb{T}^d,\mathbb{C})$ which vanishes at each $\theta$ having some coordinate $\theta_i \notin U_i$ and satisfies $\|g(\theta)\| \le 1$ for all $\theta$ obeys $\|\mu(g)\| < \varepsilon$. Second, a prescription of the values of $\mu$ on characters: for every $n \in \mathbb{Z}^d$ and every $e \in C(\mathbb{T}^d,\mathbb{C})$ with $e(\theta) = \prod_i \mathrm{fourier}(n_i)(\theta_i)$ for all $\theta$, one has $$\mu(e) = \Big(\prod_{i \ne p} [\,n_i = 0\,]\Big)\cdot\big(1 + (-1)^{q\,|n_p|}\big),$$ where the product is over the coordinates other than $p$, each factor being $1$ if $n_i = 0$ and $0$ otherwise, and $|n_p|$ is the natural absolute value of $n_p$.
--
--   The functional produced is the tensor product of two antipodal point masses in the coordinate $p$ (at $0$ and at $q/2$) with Haar probability measure in the remaining coordinates; since $d \ge 2$, mass concentrated at a point in a single coordinate spreads out over a thin box, which is what the box smallness clause records, while the Fourier values are constant along the $p$-axis. It supplies the input measure for [`AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add`](thm.html#AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add), where such a functional carries the edge contribution of the unipotent term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow
    (d : ℕ) (hd : 2 ≤ d) (p : Fin d) (q : ℕ) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
          μ e = (∏ i ∈ Finset.univ.erase p, (if n i = 0 then (1 : ℂ) else 0)) *
            (1 + (-1 : ℂ) ^ (q * (n p).natAbs)) := by sorry
