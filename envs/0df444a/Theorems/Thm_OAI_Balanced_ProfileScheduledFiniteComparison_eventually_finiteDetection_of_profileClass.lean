-- Prove2me | Theorems.Thm_OAI_Balanced_ProfileScheduledFiniteComparison_eventually_finiteDetection_of_profileClass
-- name    : OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:11:53.386977+00:00
-- url     : https://prove2.me/theorems/4bf189d3-e232-4767-8ebc-546764bf9020
-- title:
--   OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass` of [lean/OAI/Combinatorics/BalancedRyser/Profiles/ProfileFiniteScheduledLemmas.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Profiles/ProfileFiniteScheduledLemmas.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Balanced.ProfileScheduledFiniteComparison`, with `open Filter`, `open scoped Topology`, `open ProfileScheduledMarks ProfileFiniteMarks`):
--
--   ```lean
--   theorem eventually_finiteDetection_of_profileClass
--       (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
--       (hvalid : ProfileClassValid k A)
--       (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
--       {F : ℕ → Type u} [∀ t, Field (F t)] [∀ t, Fintype (F t)]
--       [∀ t, DecidableEq (F t)]
--       (D C : ∀ t, Finset (Line (F t)))
--       (hA : ∀ t, A (F t) (D t) (C t))
--       (hq : Tendsto (fun t => Fintype.card (F t)) atTop atTop)
--       (η ε : ℝ) (hε : 0 < ε) :
--       ∀ᶠ t in atTop,
--         dFinite (D t) (C t) η ε + cFinite (D t) (C t) η ε ≤
--           normalizedMean (D t) (C t) η ε +
--             32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card (F t) : ℝ) * ε^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Balanced.Line` (definitions bundle `OAIQ63Br000` of this split); `OAI.Balanced.ProfileClass`, `OAI.Balanced.ProfileClassSizeGap`, `OAI.Balanced.ProfileClassValid`, `OAI.Balanced.ProfileFiniteMarks.cFinite`, `OAI.Balanced.ProfileFiniteMarks.dFinite` and `OAI.Balanced.ProfileScheduledMarks.normalizedMean` (definitions bundle `OAIQ63Br002` of this split).
--
--   **Used by.** The proof of `OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound` of this split imports it.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Profiles/ProfileFiniteScheduledLemmas.lean (declaration OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass)

import Mathlib
import Definitions.Def_OAIQ63Br002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Filter
open scoped Topology

namespace Balanced.ProfileScheduledFiniteComparison

universe u

open ProfileScheduledMarks ProfileFiniteMarks

theorem eventually_finiteDetection_of_profileClass
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    {F : ℕ → Type u} [∀ t, Field (F t)] [∀ t, Fintype (F t)]
    [∀ t, DecidableEq (F t)]
    (D C : ∀ t, Finset (Line (F t)))
    (hA : ∀ t, A (F t) (D t) (C t))
    (hq : Tendsto (fun t => Fintype.card (F t)) atTop atTop)
    (η ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      dFinite (D t) (C t) η ε + cFinite (D t) (C t) η ε ≤
        normalizedMean (D t) (C t) η ε +
          32 * (2 * (k : ℝ) + 1)^2 / ((Fintype.card (F t) : ℝ) * ε^2) := by
  sorry

end Balanced.ProfileScheduledFiniteComparison

end

end
end

end OAI
end
