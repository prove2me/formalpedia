-- Prove2me | Theorems.Thm_MeasureTheory_aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom
-- name    : MeasureTheory.aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/f3abed7b-6207-5428-bbc0-90c544a4619b
-- title:
--   Measurability of characters in a measurable linear combination
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, together with a measurable structure that is the Borel structure of the topology, and assume $G$ is locally compact and Hausdorff. Let $\mu$ be a measure on $G$ which is a Haar measure (in particular left invariant) and regular. Let $n$ be a natural number and $\psi : \mathrm{Fin}\,n \to (G \to^* \mathbb{C})$ a family of monoid homomorphisms from $G$ to the multiplicative monoid of $\mathbb{C}$, assumed injective as a function of the index, so the $\psi_k$ are pairwise distinct. Let $c : \mathrm{Fin}\,n \to \mathbb{C}$ be scalars with $c_k \neq 0$ for every $k$. Assume the function $g \mapsto \sum_{k} c_k\,\psi_k(g)$ is a.e. strongly measurable with respect to $\mu$. Then for each index $i$ the underlying function of $\psi_i$ is itself a.e. strongly measurable with respect to $\mu$.
--
--   This is a measurability counterpart of Artin's linear independence of distinct characters: no cancellation can hide the individual characters inside a measurable linear combination with non-zero coefficients. It is used in the analysis of automorphic functions, in [`AutomorphicForm.mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt`](thm.html#AutomorphicForm.mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt), to pass from measurability of an element of a span to measurability of the characters occurring in it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Measure

theorem MeasureTheory.aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [T2Space G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    {n : ℕ} (ψ : Fin n → (G →* ℂ)) (hψ : Function.Injective ψ) (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (h : AEStronglyMeasurable (fun g => ∑ i, c i * ψ i g) μ) (i : Fin n) :
    AEStronglyMeasurable (⇑(ψ i)) μ := by sorry
