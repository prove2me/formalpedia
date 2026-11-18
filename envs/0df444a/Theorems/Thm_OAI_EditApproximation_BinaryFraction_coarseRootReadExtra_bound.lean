-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_coarseRootReadExtra_bound
-- name    : OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:24:59.332253+00:00
-- url     : https://prove2.me/theorems/cf4e8a60-0e9f-4a2a-acb1-7127207ac662
-- title:
--   OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound` of [lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseIndexedRootBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseIndexedRootBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem coarseRootReadExtra_bound {B d : ℕ} (k q L K : ℕ)
--       (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (hK : 1 ≤ K) (x y : List ℕ)
--       (draws : CoarseThresholdDraws B d)
--       (budget : CoarseReadBudget B d k (coarseEntryWidth x y) x y K) :
--       coarseRootReadExtra k q L hB hq hL x y draws ≤
--         (32 * K) * (2 * coarseActiveArrayWork k q (1 / L)
--           (coarseEntryTree B d x y) draws k + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.CoarseReadBudget` and `OAI.EditApproximation.BinaryFraction.coarseRootReadExtra` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.CoarseThresholdDraws` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.coarseEntryTree` and `OAI.EditApproximation.coarseEntryWidth` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.coarseActiveArrayWork` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseIndexedRootBound.lean (declaration OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseRootReadExtra_bound {B d : ℕ} (k q L K : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (hK : 1 ≤ K) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d)
    (budget : CoarseReadBudget B d k (coarseEntryWidth x y) x y K) :
    coarseRootReadExtra k q L hB hq hL x y draws ≤
      (32 * K) * (2 * coarseActiveArrayWork k q (1 / L)
        (coarseEntryTree B d x y) draws k + 1) := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
