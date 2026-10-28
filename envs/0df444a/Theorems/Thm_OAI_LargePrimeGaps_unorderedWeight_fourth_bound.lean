-- Prove2me | Theorems.Thm_OAI_LargePrimeGaps_unorderedWeight_fourth_bound
-- name    : OAI.LargePrimeGaps.unorderedWeight_fourth_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:54:40.75691+00:00
-- url     : https://prove2.me/theorems/ba39712a-b002-4d81-b060-b7e6dea6a86c
-- title:
--   OAI.LargePrimeGaps.unorderedWeight_fourth_bound: intermediate lemma from OpenAI, Positive lower density of large prime gaps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem344.large_gaps_and_ratio_density`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive lower density of large prime gaps*, OpenAI Math Release, September 25, 2026, result family 26, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LargePrimeGaps.unorderedWeight_fourth_bound` of [lean/OAI/NumberTheory/PrimeGaps/ProfileSymmetry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/ProfileSymmetry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LargePrimeGaps`, with `open Filter`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff`, `open Asymptotics`, `open Asymptotics`, `open Asymptotics`, `open scoped Classical`, `open scoped ContDiff`, `open Topology`, `open scoped Convolution ContDiff Pointwise`):
--
--   ```lean
--   theorem unorderedWeight_fourth_bound {tau lam : ℝ} {k : ℕ}
--       (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
--       (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
--       ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
--         average X (fun m => unorderedWeight tau lam k f X m^4)≤M
--   ```
--
--   **Definitions.** The statement is written with `OAI.LargePrimeGaps.AdmissibleFamily`, `OAI.LargePrimeGaps.average` and `OAI.LargePrimeGaps.unorderedWeight` (definitions bundle `OAIW2PG000` of this split).
--
--   **Used by.** The proof of `OAI.Problem344.large_gaps_and_ratio_density` of this split imports it.
-- source:
--   OpenAI, Positive lower density of large prime gaps, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 26; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/ProfileSymmetry.lean (declaration OAI.LargePrimeGaps.unorderedWeight_fourth_bound)

import Mathlib
import Definitions.Def_OAIW2PG000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem unorderedWeight_fourth_bound {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => unorderedWeight tau lam k f X m^4)≤M := by
  sorry

end LargePrimeGaps

end OAI
end
