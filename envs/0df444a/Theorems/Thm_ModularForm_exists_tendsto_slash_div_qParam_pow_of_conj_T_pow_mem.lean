-- Prove2me | Theorems.Thm_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem
-- name    : ModularForm.exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/9d753039-c1c3-58d5-a99e-0b93d94348bd
-- title:
--   Finite order of a non-zero modular form at a cusp
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, let $k$ be an integer and let $f$ be a modular form of weight $k$ for $\Gamma$ (in the sense of `ModularForm Γ k`: holomorphic, slash-invariant of weight $k$ under $\Gamma$ and bounded at the cusps), assumed to be non-zero. Let $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ and let $h$ be a positive natural number such that the conjugate $\sigma T^{h} \sigma^{-1}$ lies in $\Gamma$, where $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ is `ModularGroup.T`. Then there exist a natural number $n$ and a non-zero complex number $a$ such that the function $$\tau \mapsto \frac{(f\mid_k \sigma)(\tau)}{q_h(\tau)^{n}}, \qquad q_h(\tau) = e^{2\pi i \tau / h},$$ on the upper half-plane converges to $a$ along the filter `atImInfty`, i.e. as $\operatorname{Im}\tau \to \infty$. Here $f\mid_k \sigma$ is the weight-$k$ slash action of the image of $\sigma$ in $\mathrm{GL}_2(\mathbb{R})$ on the underlying function $\mathbb{H} \to \mathbb{C}$, and $q_h$ is `Function.Periodic.qParam h`. In particular the asymptotic order of vanishing of $f\mid_k\sigma$ in the parameter $q_h$ at the cusp $\sigma\infty$ is finite and equal to $n$.
--
--   This is the statement that a non-zero modular form has a well-defined finite order of vanishing in the local parameter $q_h = e^{2\pi i \tau/h}$ at a cusp $\sigma\infty$ whose width divides $h$, the basic input for defining the divisor of a modular form on a modular curve. It is used in the computation of orders of a weight-one form at the cusps of the curves $X_1(M)$, namely by [`ModularCurve.even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1`](thm.html#ModularCurve.even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm

theorem ModularForm.exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem
    (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) (h : ℕ) (hh : 0 < h) (hper : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ / Function.Periodic.qParam h τ ^ n)
        atImInfty (𝓝 a) := by sorry
