-- Prove2me | Theorems.Thm_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
-- name    : MeasureTheory.sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/5177d104-002b-5499-b1bc-a802c8aa3fa9
-- title:
--   Sup-L² bound for finite-dimensional translation-invariant spaces
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, compact, and equipped with its Borel $\sigma$-algebra, and let $\mu$ be a Haar measure on $G$ that is moreover regular. Let $V$ be a $\mathbb{C}$-submodule of the space of all functions $G \to \mathbb{C}$ which is finite-dimensional over $\mathbb{C}$, and assume: every $f \in V$ is continuous, and $V$ is stable under right translation, that is, for every $f \in V$ and every $g \in G$ the function $x \mapsto f(xg)$ again lies in $V$. The conclusion is that for every $f \in V$ and every point $x \in G$,
--   $$\|f(x)\|^2 \cdot \mu(G) \le (\dim_{\mathbb{C}} V) \cdot \int_G \|f(y)\|^2 \, d\mu(y),$$
--   where $\mu(G)$ is the real-valued measure of the whole space and $\dim_{\mathbb{C}} V$ is the `Module.finrank` of $V$, viewed as a real number. Equivalently, for the Haar probability measure, $\sup_G |f| \le \sqrt{\dim_{\mathbb{C}} V}\, \|f\|_{L^2(\mu)}$, with a constant depending only on $\dim_{\mathbb{C}} V$.
--
--   This is the reproducing-kernel (Bergman-type) estimate bounding the pointwise size of a function in a finite-dimensional right-translation-invariant space of continuous functions on a compact group by its $L^2$-norm, the bound being uniform in the point and depending only on the dimension. It is used to obtain uniform bounds on automorphic forms and on their values under intertwining operators over the maximal compact subgroup of the adelic group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hcont : ∀ f ∈ V, Continuous f)
    (hinv : ∀ f ∈ V, ∀ g : G, (fun x => f (x * g)) ∈ V) :
    ∀ f ∈ V, ∀ x : G,
      ‖f x‖ ^ 2 * μ.real Set.univ ≤ (Module.finrank ℂ V : ℝ) * ∫ y, ‖f y‖ ^ 2 ∂μ := by sorry
