-- Prove2me | Theorems.Thm_MaxPressure_StrictLeontief_max_attained_on_extreme
-- name    : MaxPressure.StrictLeontief.max_attained_on_extreme
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:55:48.233363+00:00
-- url     : https://prove2.me/theorems/0288671d-40b9-431a-831a-b2bef2d276ab
-- title:
--   §3, p. 201 — the maximum of the network pressure over the allocations is achieved at an extreme allocation
-- statement:
--   Consider a stochastic processing network satisfying the standing assumptions of §2, whose allocation set $\mathcal A$ is nonempty, and let $\mathcal E$ be the set of extreme allocations. Then for every buffer-level vector $z\in\mathbb R^I_+$ there is an extreme allocation $a^*\in\mathcal E$ with
--   $$p(a^*,z)=\max_{a\in\mathcal A}p(a,z),$$
--   that is, $p(a,z)\le p(a^*,z)$ for every $a\in\mathcal A$.
--
--   Because $p(a,z)=z\cdot Ra$ is linear in $a$ and $\mathcal A$ is a bounded polyhedron, a maximum pressure allocation can always be chosen among the finitely many extreme allocations. This is the fact that makes the maximum pressure policy of Definition 1 well defined, and the proof of Theorem 6 uses it to start from an extreme maximizer.
--
--   **Formalization Note** Nonemptiness of $\mathcal A$ is an explicit hypothesis: the paper presupposes it (it lists $\mathcal E=\{a^1,\dots,a^E\}$), but the standing assumptions alone do not imply it when input activities share input processors. "Maximum" is stated in domination form.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 201, §3, sentence after (7)

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

namespace MaxPressure.StrictLeontief

/-- §3, p. 201: since `p(a, z)` is linear in `a`, the maximum of `p(·, z)` over the
allocation set `𝒜` is achieved at an extreme allocation. -/
theorem max_attained_on_extreme {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hA : (allocSet N).Nonempty) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∃ a ∈ extremeAllocs N, ∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N a z := by sorry

end MaxPressure.StrictLeontief
