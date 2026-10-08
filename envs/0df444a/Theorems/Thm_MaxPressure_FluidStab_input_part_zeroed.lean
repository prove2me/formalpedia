-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_input_part_zeroed
-- name    : MaxPressure.FluidStab.input_part_zeroed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:54:17.464135+00:00
-- url     : https://prove2.me/theorems/626866c4-c46f-4039-9970-da4db1b75a27
-- title:
--   Proof of Theorem 5, p. 215 — under Assumption 2 there is x̂ ≥ 0 with Rx̂ > 0 vanishing on input activities and input processors
-- statement:
--   Let a stochastic processing network satisfy the standing assumptions of §2 and Assumption 2 (there is $x\ge0$ with $Rx>0$). Then there is a vector $\hat x\in\mathbb R^J$ such that
--
--   1. $\hat x\ge0$ and $R\hat x>0$ componentwise;
--   2. $\hat x_j=0$ for every input activity $j$;
--   3. $\sum_jA_{kj}\hat x_j=0$ for every input processor $k$.
--
--   In the proof of Theorem 5 this vector is the direction along which an LP solution with $\rho<1$ is pushed to obtain an allocation with strictly positive net outflow from every buffer, without changing the load on the input processors.
--
--   **Formalization Note** "$Rx>0$" is componentwise strict positivity on every internal buffer.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 215, proof of Theorem 5 (App. B), sentences 2–4

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- Proof of Theorem 5, App. B, p. 215: from Assumption 2 there is an `x̂ ≥ 0` with `Rx̂ > 0`;
`x̂_j` can be set to `0` for each input activity `j` so that `Rx̂ > 0` still holds, and then
`∑_j A_kj x̂_j = 0` for each input processor `k`. -/
theorem input_part_zeroed {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (h2 : Assumption2 N) :
    ∃ xh : Fin J → ℝ, (∀ j, 0 ≤ xh j) ∧ (∀ i, 0 < (R N *ᵥ xh) i) ∧
      (∀ j, IsInputActivity N j → xh j = 0) ∧
      (∀ k, N.inputProc k → ∑ j, N.A k j * xh j = 0) := by sorry

end MaxPressure.FluidStab
