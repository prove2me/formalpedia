-- Prove2me | Theorems.Thm_GeneratesNS_growth_const_pos
-- name    : GeneratesNS.growth_const_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:14:58.958712+00:00
-- url     : https://prove2.me/theorems/cb5ba3a4-e63c-420f-9230-87cff3c81129
-- title:
--   GeneratesNS.growth_const_pos: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `GeneratesNS`, with `open Subgroup`, `open scoped Finset`, `open scoped Pointwise`, `open scoped commutatorElement`, `open Generates`, `open scoped RealInnerProductSpace`, `open MeasureTheory`, `open Additive`):
--
--   ```lean
--   lemma growth_const_pos {d a : ℕ} (ha: ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d): 0 < a
--   ```
--
--   **Definitions.** The statement is written with `Generates`, `GeneratesNS.G_dec_eq` and `GeneratesNS.G_group` (definitions bundle `OAIQ093D000` of this split).
--
--   **Used by.** The proof of `GeneratesNS.theorem_3_1` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D000

section

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

set_option maxHeartbeats 1000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

lemma growth_const_pos {d a : ℕ} (ha: ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d): 0 < a := by
  sorry

end GeneratesNS
end
