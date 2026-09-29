-- Prove2me | Theorems.Thm_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
-- name    : MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/dae9c30f-1280-5c8b-9807-3a3d102e7fb5
-- title:
--   Godement's finite-dimensionality lemma for subspaces of L²
-- statement:
--   Let $X$ be a measurable space carrying a finite measure $\mu$, let $\mathbb{k}$ be $\mathbb{R}$ or $\mathbb{C}$ (an `RCLike` field), and let $V$ be a $\mathbb{k}$-submodule of $L^2(\mu;\mathbb{k})$, the space of (classes of) square-integrable $\mathbb{k}$-valued functions on $X$. Let $C$ be a real number, not assumed nonnegative, and assume that every $\varphi \in V$ satisfies the pointwise bound $\|\varphi(x)\| \le C\,\|\varphi\|$ for $\mu$-almost every $x \in X$, where $\varphi(x)$ is evaluated through the coercion of the $L^2$-class to a function $X \to \mathbb{k}$ and $\|\varphi\|$ is its $L^2$-norm. The conclusion is a conjunction: $V$ is a finite-dimensional $\mathbb{k}$-vector space, and its rank satisfies $$\operatorname{finrank}_{\mathbb{k}} V \le C^2 \cdot \mu(X),$$ the inequality being an inequality of real numbers, with $\operatorname{finrank}_{\mathbb{k}} V$ cast from $\mathbb{N}$ and $\mu(X) = \mu(\mathrm{univ})$ replaced by its real part `(μ Set.univ).toReal`.
--
--   This is Godement's lemma: a space of square-integrable functions on a finite measure space whose sup-norm is dominated by a fixed multiple of the $L^2$-norm is finite-dimensional, with an explicit bound on the dimension. It is used in the form [`MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict`](thm.html#MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict), where the bound is stated for a restricted measure and the $L^2$-norm written as an `eLpNorm`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (Lp 𝕜 2 μ)) (C : ℝ)
    (hV : ∀ φ ∈ V, ∀ᵐ x ∂μ, ‖(φ : X → 𝕜) x‖ ≤ C * ‖φ‖) :
    FiniteDimensional 𝕜 V ∧ (Module.finrank 𝕜 V : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := by sorry
