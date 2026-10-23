-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_lemma_4_traced
-- name    : HochbaumShmoys.Uniform.lemma_4_traced
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:42.775926+00:00
-- url     : https://prove2.me/theorems/4f2f5458-2a4a-49d4-85be-a72f955ad5ce
-- title:
--   §3, proof of Lemma 4 — every packing traced from a path is $(2\varepsilon+\varepsilon^2)$-relaxed feasible (pp. 548–549)
-- statement:
--   Let $N\ge2$, $\delta=1/N$, $m\ge1$, and consider a normalized instance: bins $\beta_1\ge\dots\ge\beta_m>0$ with $\beta_1=1$, pieces $0<\pi_j\le1$. Let $\sigma$ be any packing traced from an initial–success path of the layered graph by the rules of the proof of Lemma 4 (large and medium pieces according to the path's configurations, small pieces one at a time into bins with positive usable slack). Then for every bin $t$,
--   $$\sum_{j:\ \sigma(j)=t}\pi_j\le(1+2\delta+\delta^2)\,\beta_t .$$
--
--   This is the form in which the proof of Lemma 4 establishes it, and the form needed to say that every output of all-pack, however its arbitrary choices are made, is $(2\delta+\delta^2)$-relaxed feasible.
--
--   **Formalization Note** The paper states Lemma 4 as the existence of a relaxed feasible packing; its proof shows that the packing it constructs from the path is one. This item states that construction's guarantee for every way of making the construction's arbitrary choices. Hypotheses are the standing assumptions of §3.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, pp. 548–549, §3, proof of Lemma 4 — the traced packing is (2ε + ε²)-relaxed feasible

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph

namespace HochbaumShmoys.Uniform

theorem lemma_4_traced (N : ℕ) (hN : 2 ≤ N) (m n : ℕ) (hm : 0 < m) (β : Fin m → ℝ)
    (π : Fin n → ℝ)
    (hβ : Antitone β) (hβ0 : β ⟨0, hm⟩ = 1) (hβpos : ∀ t, 0 < β t)
    (hπ : ∀ j, 0 < π j ∧ π j ≤ 1)
    (σ : Fin n → Fin m) (hσ : IsTracedPacking N β π σ) :
    IsRelaxedFeasible (2 * (N : ℝ)⁻¹ + ((N : ℝ)⁻¹) ^ 2) π β σ := by sorry

end HochbaumShmoys.Uniform
