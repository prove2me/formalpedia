-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_max_pressure_at_extreme
-- name    : MaxPressure.FluidStab.max_pressure_at_extreme
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:54:25.532761+00:00
-- url     : https://prove2.me/theorems/1b8fe1fc-1bac-4e85-9706-378e03daf0fb
-- title:
--   §3, p. 201 — the maximum of p(·, z) over 𝒜 is achieved at an extreme allocation
-- statement:
--   Let a stochastic processing network satisfy the standing assumptions of §2 and have a nonempty allocation set $\mathcal A$. For every buffer-level vector $z\in\mathbb R^I_+$ there is an extreme allocation $a^*\in\mathcal E$ with
--   $$p(a^*,z)=\max_{a\in\mathcal A}p(a,z),$$
--   that is, $p(a,z)\le p(a^*,z)$ for every $a\in\mathcal A$. In particular $\max_{a\in\mathcal A}p(a,z)=\max_{a\in\mathcal E}p(a,z)$.
--
--   The pressure $p(a,z)=z\cdot Ra$ is linear in $a$ and $\mathcal A$ is a bounded polyhedron, so the maximum is attained at a vertex. This is what lets the maximum pressure equation (20), stated over $\mathcal E$, be compared with any feasible allocation in $\mathcal A$.
--
--   **Formalization Note** Nonemptiness of $\mathcal A$ is presupposed by the page ("the input processors are never idle") and added as a hypothesis: the standing assumptions alone do not imply it (three input processors $k_1,k_2,k_3$ and two input activities needing $\{k_1,k_2\}$ and $\{k_2,k_3\}$ make (2) infeasible). Boundedness of $\mathcal A$ comes from the standing assumption that every activity needs a processor.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 201, §3, after (7)

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- §3, p. 201: `p(a, z)` is linear in `a`, so the maximum in (7) is achieved at one of the
extreme allocations: for every `z ∈ ℝ^I_+` there is `a* ∈ ℰ` with
`p(a*, z) = max_{a ∈ 𝒜} p(a, z) = max_{a ∈ ℰ} p(a, z)`. The hypothesis that `𝒜` is nonempty
is presupposed by the page. -/
theorem max_pressure_at_extreme {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hne : (allocSet N).Nonempty) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∃ e ∈ extremeAllocs N, ∀ a ∈ allocSet N, pressure N a z ≤ pressure N e z := by sorry

end MaxPressure.FluidStab
