-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryPhysicalInitial_width
-- name    : OAI.EditApproximation.queryPhysicalInitial_width
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:22:14.662261+00:00
-- url     : https://prove2.me/theorems/50e409f1-8d73-480d-b555-aaf88ecca81e
-- title:
--   OAI.EditApproximation.queryPhysicalInitial_width: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryPhysicalInitial_width` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryPhysicalInitialCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryPhysicalInitialCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem queryPhysicalInitial_width (q : TargetInterval target.length)
--       (hP : 0 < P) (hleaf : Nat.size (target.length + 1) + 2 ≤ B)
--       (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B) :
--       ((queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q).value
--         oracle).width ≤ B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo` and `OAI.EditApproximation.PositionCounts` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.BitQuery.value` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest`, `OAI.EditApproximation.PhysicalTableRequest` and `OAI.EditApproximation.PhysicalTableRequest.Bounded` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.queryPhysicalInitial` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound` and `OAI.EditApproximation.queryChargedFamilyTable_width` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryPhysicalInitialCost.lean (declaration OAI.EditApproximation.queryPhysicalInitial_width)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_15

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Initial
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F Amax B C : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryPhysicalInitial_width (q : TargetInterval target.length)
    (hP : 0 < P) (hleaf : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B) :
    ((queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q).value
      oracle).width ≤ B := by
  sorry

end Initial
end EditApproximation

end OAI
end
