-- Prove2me | Theorems.Thm_HnEpsData_H_n_contradiction
-- name    : HnEpsData.H_n_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:19:42.144701+00:00
-- url     : https://prove2.me/theorems/e33c9316-be4c-4abc-bcf1-3c57b9221a96
-- title:
--   HnEpsData.H_n_contradiction: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `HnEpsData`, with `open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace`, `open Subgroup Pointwise Finset`, `open scoped Pointwise Finset`, `open scoped commutatorElement IsMulCommutative`):
--
--   ```lean
--   lemma H_n_contradiction (data : HnData)
--     (c: ℝ)
--     (c_pos: 0 < c)
--     (c_lt: c < 1 / 40)
--     (c_mul_pos: 1 ≤ c * (H_n_eps data.hd)⁻¹)
--     (eps_div_lt: (H_n_eps data.hd) < c / (Real.exp (4 + ↑data.S_poly_deg * Real.log 2) + 1))
--     : False
--   ```
--
--   **Definitions.** The statement is written with `HnEpsData`, `HnEpsData.H_n_eps` and `HnEpsData.HnData` (definitions bundle `OAIQ093D001` of this split).
--
--   **Used by.** The proof of `HnEpsData.central_trivial_virtually_abelian` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D001

section

attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative

namespace HnEpsData

variable [h_n_eps_data: HnEpsData]

lemma H_n_contradiction (data : HnData)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40)
  (c_mul_pos: 1 ≤ c * (H_n_eps data.hd)⁻¹)
  (eps_div_lt: (H_n_eps data.hd) < c / (Real.exp (4 + ↑data.S_poly_deg * Real.log 2) + 1))
  : False := by
  sorry

open scoped Pointwise

end HnEpsData

end
