-- Prove2me | Theorems.Thm_HnEpsData_central_trivial_virtually_abelian
-- name    : HnEpsData.central_trivial_virtually_abelian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:20:24.813021+00:00
-- url     : https://prove2.me/theorems/c402f7a0-9697-428b-b562-636ee2952c27
-- title:
--   HnEpsData.central_trivial_virtually_abelian: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `HnEpsData`, with `open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace`, `open Subgroup Pointwise Finset`, `open scoped Pointwise Finset`, `open scoped commutatorElement IsMulCommutative`, `open scoped Pointwise`):
--
--   ```lean
--   lemma central_trivial_virtually_abelian (n : ℕ) (hn : 2 ≤ n) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG)
--     (G'_central_trivial : ∀ g : (G' n (H_n_eps hn) G), g ∈ Set.center (G' n (H_n_eps hn) G) → ∃ z : ℂ, g.val.val.val = z • 1)
--     (G'_finite_index: (G' n (H_n_eps hn) G).FiniteIndex)
--     (S_poly_data: SPolyData (G' n (H_n_eps hn) G))
--
--     (data_eq_degree: h_n_eps_data.degree = S_poly_data.S_poly_deg)
--     : ∃ N : Subgroup G, IsMulCommutative N ∧ N.FiniteIndex
--   ```
--
--   **Definitions.** The statement is written with `G'` (definitions bundle `OAIQ093D000` of this split); `HnEpsData`, `SPolyData` and `HnEpsData.H_n_eps` (definitions bundle `OAIQ093D001` of this split).
--
--   **Used by.** The proof of `compact_lie_virtually_abelian` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D000
import Definitions.Def_OAIQ093D001

section

attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
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

open scoped Pointwise

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 2200000 in
lemma central_trivial_virtually_abelian (n : ℕ) (hn : 2 ≤ n) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG)
  (G'_central_trivial : ∀ g : (G' n (H_n_eps hn) G), g ∈ Set.center (G' n (H_n_eps hn) G) → ∃ z : ℂ, g.val.val.val = z • 1)
  (G'_finite_index: (G' n (H_n_eps hn) G).FiniteIndex)
  (S_poly_data: SPolyData (G' n (H_n_eps hn) G))

  (data_eq_degree: h_n_eps_data.degree = S_poly_data.S_poly_deg)
  : ∃ N : Subgroup G, IsMulCommutative N ∧ N.FiniteIndex := by
  sorry

end HnEpsData

end
