-- Prove2me | Theorems.Thm_NumberField_subgroup_eq_top_of_forall_inertia_le
-- name    : NumberField.subgroup_eq_top_of_forall_inertia_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/faae6af3-4e15-54d9-9e27-296246ccd72d
-- title:
--   Inertia subgroups generate Gal(K/ℚ)
-- statement:
--   Let $K$ be a field which is a number field and which is Galois over $\mathbb{Q}$, and let $H$ be a subgroup of the group $K \simeq_{\mathbb{Q}} K$ of $\mathbb{Q}$-algebra automorphisms of $K$. Assume that for every ideal $P$ of the ring of integers $\mathcal{O}_K =$ `NumberField.RingOfIntegers K` which is maximal, the inertia subgroup `P.inertia (K ≃ₐ[ℚ] K)` of $P$ for the action of the full automorphism group is contained in $H$. The conclusion is that $H$ is the whole group, $H = \top$. Thus a subgroup of $\mathrm{Gal}(K/\mathbb{Q})$ containing the inertia group of every maximal ideal of $\mathcal{O}_K$ is everything; equivalently, the inertia subgroups at the finite places generate $\mathrm{Gal}(K/\mathbb{Q})$. Note that the hypothesis ranges over all maximal ideals of $\mathcal{O}_K$, with no choice of decomposition made, and that inertia is taken in Mathlib's sense for the Galois action on $\mathcal{O}_K$.
--
--   This is the number-field-level form of the statement that $\mathbb{Q}$ admits no nontrivial everywhere-unramified extension (Minkowski), phrased through the Galois correspondence. It is used to deduce the corresponding assertion for subgroups of the absolute Galois group of $\mathbb{Q}$ in [`AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le`](thm.html#AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le), the input to the triviality of everywhere-unramified characters of $G_{\mathbb{Q}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_subgroup_eq_top_of_forall_inertia_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.subgroup_eq_top_of_forall_inertia_le {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] (H : Subgroup (K ≃ₐ[ℚ] K)) (hH : ∀ P : Ideal (NumberField.RingOfIntegers K), P.IsMaximal → P.inertia (K ≃ₐ[ℚ] K) ≤ H) : H = ⊤ := by sorry
