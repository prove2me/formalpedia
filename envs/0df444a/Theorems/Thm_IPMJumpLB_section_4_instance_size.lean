-- Prove2me | Theorems.Thm_IPMJumpLB_section_4_instance_size
-- name    : IPMJumpLB.section_4_instance_size
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:29:20.466194+00:00
-- url     : https://prove2.me/theorems/ce119bd2-0ae9-4eff-9477-9bb340adc7e4
-- title:
--   Section 4 — instance size and $\eta = \alpha\hat n_k \ge 6k^2 \ge 2N_k$
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$ and $\eta = \alpha \hat n_k$. The unit-demand instance of Section 4 has
--   $$
--   \hat n_k = bk^2 + 1 \ \text{vertices}, \qquad \hat m_k = (2b-2)k^2 + k \ \text{arcs},
--   $$
--   and, with $N_k = 2k^2 + k$ the number of path arcs and leaf arcs,
--   $$
--   \eta = \alpha \hat n_k \ \ge\ 6k^2 \ \ge\ 2N_k .
--   $$
--
--   The bound $\eta \ge 2N_k$ is what makes the path and leaf arcs carry at most half of the duality gap at every $\eta$-iterate.
--
--   **Formalization Note** The cardinalities are those of the vertex and arc types; $b$ and $\eta$ enter through defining equations.
--
--   Differences from the source:
--   - encoding: b = ⌈6/α⌉ and η = α n̂_k as fixed values → variables b, η with hypotheses b = ⌈6/α⌉₊ and η = α·n̂_k; reason: names for the paper's values, same instances
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 4, p.11 (display of n̂_k, m̂_k and the sentence "The number of shortcut paths ensures η = αn̂_k ≥ 6k² ≥ 2N_k")

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat
import Definitions.Def_IPMJumpLB_mHat

namespace IPMJumpLB

/-- Section 4, instance size and the size of `η` (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §4, p.11): for `α ∈ (0, 1)`,
`b = ⌈6/α⌉` and `k ≥ 3`, the instance has `n̂_k = bk² + 1` vertices and `m̂_k = (2b − 2)k² + k`
arcs, and `η = α n̂_k ≥ 6k² ≥ 2N_k` with `N_k = 2k² + k`. -/
theorem section_4_instance_size (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ)) :
    Fintype.card (VertexU b k) = nHat b k ∧ Fintype.card (ArcU b k) = mHat b k ∧
      6 * (k : ℝ) ^ 2 ≤ η ∧ 2 * (2 * (k : ℝ) ^ 2 + k) ≤ 6 * (k : ℝ) ^ 2 := by sorry

end IPMJumpLB
