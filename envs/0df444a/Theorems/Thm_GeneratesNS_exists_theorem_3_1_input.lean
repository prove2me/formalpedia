-- Prove2me | Theorems.Thm_GeneratesNS_exists_theorem_3_1_input
-- name    : GeneratesNS.exists_theorem_3_1_input
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:14:29.229734+00:00
-- url     : https://prove2.me/theorems/42e91e1b-2622-4c43-9806-e67856e56c7f
-- title:
--   GeneratesNS.exists_theorem_3_1_input: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `GeneratesNS`, with `open Subgroup`, `open scoped Finset`, `open scoped Pointwise`, `open scoped commutatorElement`, `open Generates`, `open scoped RealInnerProductSpace`, `open MeasureTheory`, `open MeasureTheory`):
--
--   ```lean
--   lemma exists_theorem_3_1_input [hGS: Generates ] {d: ℕ} (hd: HasPolynomialGrowthD S d): Nonempty (Theorem3_1_Input G)
--   ```
--
--   **Definitions.** The statement is written with `Generates`, `HasPolynomialGrowthD`, `GeneratesNS.G_dec_eq` and `GeneratesNS.G_group` (definitions bundle `OAIQ093D000` of this split); `GeneratesNS.Theorem3_1_Input` (definitions bundle `OAIQ093D001` of this split).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.group_recognition` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D000
import Definitions.Def_OAIQ093D001

section

attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

open MeasureTheory

open MeasureTheory

omit hGS in
lemma exists_theorem_3_1_input [hGS: Generates ] {d: ℕ} (hd: HasPolynomialGrowthD S d): Nonempty (Theorem3_1_Input G) := by
  sorry

end GeneratesNS
end
