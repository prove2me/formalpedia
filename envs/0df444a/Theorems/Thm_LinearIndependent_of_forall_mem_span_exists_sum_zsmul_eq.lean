-- Prove2me | Theorems.Thm_LinearIndependent_of_forall_mem_span_exists_sum_zsmul_eq
-- name    : LinearIndependent.of_forall_mem_span_exists_sum_zsmul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/13c63671-d12c-5fe8-9c6e-9716b89e3c07
-- title:
--   ℤ-generators of a full lattice are ℝ-independent
-- statement:
--   Let $V$ be an additive commutative group equipped with a real vector space structure, let $k$ be a natural number, let $b_0$ be a basis of $V$ over $\mathbb{R}$ indexed by $\mathrm{Fin}\,k$, and let $v : \mathrm{Fin}\,k \to V$ be a family of $k$ vectors. Assume that every element $x$ of the $\mathbb{Z}$-submodule of $V$ spanned by the range of $b_0$ — that is, of the lattice $L = \sum_i \mathbb{Z} b_{0,i}$ — admits integers $n_i$ with $\sum_i n_i \cdot v_i = x$, the scalars acting by $\mathbb{Z}$-scalar multiplication. The conclusion is that the family $v$ is linearly independent over $\mathbb{R}$. Note that the $v_i$ are not assumed to lie in $L$, nor is any uniqueness of the integer coefficients $n_i$ assumed; only that the $v_i$ generate $L$ as a $\mathbb{Z}$-module in the weak sense stated. Since the index type has $k$ elements and $\dim_{\mathbb{R}} V = k$, the conclusion is equivalent to $v$ being an $\mathbb{R}$-basis of $V$, though only linear independence is asserted.
--
--   This is the standard linear-algebra step turning a $\mathbb{Z}$-generating family of a full lattice in a real vector space into an $\mathbb{R}$-linearly independent family, hence an $\mathbb{R}$-basis. It is used to show that a holomorphic $\mathbb{Z}$-basis of the period lattices in a family of complex tori gives well-defined real frame coordinates, as in [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_lambdaAction_frameCoords_of_uniformization_family_of_smooth`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_lambdaAction_frameCoords_of_uniformization_family_of_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearIndependent_of_forall_mem_span_exists_sum_zsmul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearIndependent.of_forall_mem_span_exists_sum_zsmul_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (b₀ : Module.Basis (Fin k) ℝ V) (v : Fin k → V)
    (hgen : ∀ x ∈ Submodule.span ℤ (Set.range b₀), ∃ n : Fin k → ℤ, (∑ i, n i • v i) = x) :
    LinearIndependent ℝ v := by sorry
