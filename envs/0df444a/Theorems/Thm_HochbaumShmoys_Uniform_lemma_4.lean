-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_lemma_4
-- name    : HochbaumShmoys.Uniform.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:05.426373+00:00
-- url     : https://prove2.me/theorems/0af9acb7-eab1-47a2-8e6e-dcdc629a88ee
-- title:
--   Lemma 4 — a path from initial to success gives a $(2\varepsilon+\varepsilon^2)$-relaxed feasible packing (p. 548)
-- statement:
--   Let $N\ge2$, $\delta=1/N$, $m\ge1$, and consider a normalized instance: bins $\beta_1\ge\dots\ge\beta_m>0$ with $\beta_1=1$, pieces $0<\pi_j\le1$. If the layered graph of all-pack for this instance contains a directed path from the initial node to success, then there is a $(2\delta+\delta^2)$-relaxed feasible packing, i.e. a map $\sigma$ with
--   $$\sum_{j:\ \sigma(j)=t}\pi_j\le(1+2\delta+\delta^2)\,\beta_t\quad\text{for every bin }t .$$
--
--   With Lemma 3 this makes all-pack a $(2\delta+\delta^2)$-relaxed decision procedure.
--
--   **Formalization Note** Stated as printed (existence). The stronger form, that every packing traced from a path is relaxed feasible, is the separate item for the proof of Lemma 4. Hypotheses are the standing assumptions of §3.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 548, Lemma 4

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph

namespace HochbaumShmoys.Uniform

theorem lemma_4 (N : ℕ) (hN : 2 ≤ N) (m n : ℕ) (hm : 0 < m) (β : Fin m → ℝ) (π : Fin n → ℝ)
    (hβ : Antitone β) (hβ0 : β ⟨0, hm⟩ = 1) (hβpos : ∀ t, 0 < β t)
    (hπ : ∀ j, 0 < π j ∧ π j ≤ 1)
    (hpath : Relation.ReflTransGen (Arc N β π) (initialNode N π hm) Node.success) :
    ∃ σ : Fin n → Fin m,
      IsRelaxedFeasible (2 * (N : ℝ)⁻¹ + ((N : ℝ)⁻¹) ^ 2) π β σ := by sorry

end HochbaumShmoys.Uniform
