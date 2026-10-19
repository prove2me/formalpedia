-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_observation_3_1
-- name    : ImprovedMMS.Additive.observation_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:18.779566+00:00
-- url     : https://prove2.me/theorems/78cef31c-1f7b-4cf0-917a-33cf7f877067
-- title:
--   Observation 3.1, p. 20 — in a topological ordering, V_i(f_j) ≤ 3/4 − ϵ_i whenever a_j ≺_O a_i
-- statement:
--   Let $C$ be a cycle-envy-free set of semi-satisfied agents and $\prec_O$ a topological ordering of $C$. Then for all agents $a_i,a_j\in C$ with $a_j\prec_O a_i$,
--   $$V_i(f_j)\ \le\ 3/4-\epsilon_i,$$
--   where $\epsilon_i=3/4-V_i(f_i)$.
--
--   It lets the bag-filling phase serve agents in the topological order without creating envy towards earlier agents.
--
--   **Formalization Note** The ordering is positions `pos` injective on $C$ in which every envy edge goes forward (the remark after Definition 3.12, p. 20); $a_j\prec_O a_i$ is `pos j < pos i`.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 20, Observation 3.1 (Definition 3.12)

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Envy

namespace ImprovedMMS.Additive

/-- Observation 3.1 (p. 20): for a cycle-envy-free set `C` of semi-satisfied agents and a
topological ordering `≺_O` of `C`, if `a_j ≺_O a_i` then `V_i(f_j) ≤ 3/4 − ϵ_i`. -/
theorem observation_3_1 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (f g : Fin n → Finset (Fin m))
    (C : Finset (Fin n)) (hC : ∀ i ∈ C, IsSemiSatisfied f g i) (hcef : IsCycleEnvyFree v f C)
    (pos : Fin n → ℕ) (hpos : IsTopologicalOrder v f C pos) :
    ∀ i ∈ C, ∀ j ∈ C, pos j < pos i → v i (f j) ≤ 3 / 4 - eps v f i := by sorry

end ImprovedMMS.Additive
