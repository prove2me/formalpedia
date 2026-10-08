-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_input_column_R_nonpos
-- name    : MaxPressure.FluidStab.input_column_R_nonpos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:54:05.458988+00:00
-- url     : https://prove2.me/theorems/3c44ad08-2937-4473-82a2-9a922ad8a81e
-- title:
--   Proof of Theorem 5, p. 215 — for an input activity j, R_ij = −μ_j B_j0 P^j_{0i} ≤ 0
-- statement:
--   Let a stochastic processing network satisfy the standing assumptions of §2, and let $R$ be its input-output matrix (5). If $j$ is an input activity (its constituency is $\{0\}$), then for every internal buffer $i$
--   $$R_{ij}=-\mu_jB_{j0}P^j_{0i}\le0 .$$
--
--   An input activity only moves jobs from the outside into the network, so it is a net producer of material in every internal buffer. This is the first step of the proof of Theorem 5: it allows the input part of the vector of Assumption 2 to be discarded.
--
--   **Formalization Note** Buffer $i$ of the page is the index `i.succ` of `Fin (I+1)`. The inequality uses $\mu_j>0$ and $P^j\ge0$ from the standing assumptions.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 215, proof of Theorem 5 (App. B), second sentence

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- Proof of Theorem 5, App. B, p. 215: for each input activity `j`,
`R_ij = −μ_j B_j0 P^j_{0i} ≤ 0` for every internal buffer `i`. -/
theorem input_column_R_nonpos {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (j : Fin J) (hj : IsInputActivity N j) (i : Fin I) :
    R N i j = -(μ N j * N.B j 0 * N.P j 0 i.succ) ∧ R N i j ≤ 0 := by sorry

end MaxPressure.FluidStab
