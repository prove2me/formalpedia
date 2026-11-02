-- Prove2me | Theorems.Thm_GeneratesNS_word_norm_pow
-- name    : GeneratesNS.word_norm_pow
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:22:04.832196+00:00
-- url     : https://prove2.me/theorems/094e2199-d0be-4d9a-ae93-a712ba44d30e
-- title:
--   GeneratesNS.word_norm_pow: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `GeneratesNS`, with `open Subgroup`, `open scoped Finset`, `open scoped Pointwise`, `open scoped commutatorElement`, `open Generates`):
--
--   ```lean
--   lemma word_norm_pow (x : G) (n: ℕ): WordNorm (x^n) ≤ n * WordNorm x
--   ```
--
--   **Definitions.** The statement is written with `Generates`, `GeneratesNS.G_group` and `GeneratesNS.WordNorm` (definitions bundle `OAIQ093D000` of this split).
--
--   **Used by.** The proof of `GeneratesNS.theorem_3_1` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D000

section

attribute [-instance] _root_.GeneratesNS.LipschitzH.add _root_.GeneratesNS.LipschitzH.addMonoid _root_.GeneratesNS.LipschitzH.instAddCommGroup _root_.GeneratesNS.LipschitzH.instAddCommMonoid _root_.GeneratesNS.LipschitzH.zero _root_.GeneratesNS.LipschitzH_seminorm _root_.GeneratesNS.WordDist.instBorelSpace _root_.GeneratesNS.WordDist.instBorelSpaceAddOpp _root_.GeneratesNS.WordDist.instMeasurableSpace _root_.GeneratesNS.WordDist.instMeasureableSpaceOpp _root_.GeneratesNS.WordDist.measureSpace _root_.GeneratesNS.countable_G _root_.GeneratesNS.countable_add_G _root_.GeneratesNS.discreteTopology _root_.GeneratesNS.fintype_closedBall _root_.GeneratesNS.instContinuousInvG _root_.GeneratesNS.instContinuousMulG _root_.GeneratesNS.instFunLikeLipschitzHGReal _root_.GeneratesNS.instIsTopologicalGroupG _root_.GeneratesNS.isometricGMul _root_.GeneratesNS.lipschitzHVectorSpace _root_.GeneratesNS.lipschitzSMul _root_.GeneratesNS.my_add_haar_right_invariant _root_.GeneratesNS.negLipschitzH _root_.GeneratesNS.subLipschithZ _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

lemma word_norm_pow (x : G) (n: ℕ): WordNorm (x^n) ≤ n * WordNorm x := by
  sorry

end GeneratesNS
end
