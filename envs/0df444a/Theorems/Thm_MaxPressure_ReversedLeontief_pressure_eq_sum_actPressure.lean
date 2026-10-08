-- Prove2me | Theorems.Thm_MaxPressure_ReversedLeontief_pressure_eq_sum_actPressure
-- name    : MaxPressure.ReversedLeontief.pressure_eq_sum_actPressure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:06:28.254177+00:00
-- url     : https://prove2.me/theorems/b3dc0423-3fc7-4352-aaef-dde123d45ef8
-- title:
--   §8, p. 208 — total pressure is the weighted sum of activity pressures
-- statement:
--   Let $R$ be the input-output matrix of a stochastic processing network, $p(a,z)=z\cdot Ra$ the network pressure and $p(j,z)=\sum_{i\in\mathcal I}R_{ij}z_i$ the pressure of activity $j$. For every vector $a\in\mathbb R^J$ and every $z\in\mathbb R^I$,
--   $$p(a,z)=\sum_{j\in\mathcal J}a_j\,p(j,z).$$
--
--   This identity reduces the network pressure, which is linear in the allocation, to the pressures of the individual activities; it is the starting point of the processor-by-processor description of maximum pressure allocations (Lemma 3).
--
--   **Formalization Note.** The page states it for allocations; the Lean statement holds for every vector $a$ and every $z$, with no network assumptions.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 208, §8, display after (30)

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- §8, p. 208: the total network pressure is the `a`-weighted sum of the activity pressures,
`p(a, z) = ∑_j a_j p(j, z)`, for every vector `a` and every `z`. -/
theorem pressure_eq_sum_actPressure {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N a z = ∑ j, a j * actPressure N j z := by sorry

end MaxPressure.ReversedLeontief
