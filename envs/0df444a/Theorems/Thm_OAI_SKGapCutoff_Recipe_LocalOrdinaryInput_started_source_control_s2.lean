-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_LocalOrdinaryInput_started_source_control_s2
-- name    : OAI.SKGapCutoff.Recipe.LocalOrdinaryInput.started_source_control_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:51:59.961499+00:00
-- url     : https://prove2.me/theorems/f756c113-52bd-4808-9e60-6597d756149d
-- title:
--   OAI.SKGapCutoff.Recipe.LocalOrdinaryInput.started_source_control_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe.LocalOrdinaryInput`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial`):
--
--   ```lean
--   lemma started_source_control_s2 (a : ℕ) (ha : a≤N) :
--       TraceControl (D.startedNodeSourceError w y T x a) (c.startedSourceCost D.j (Fintype.card ι) (Fintype.card σ) B a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGapCutoff.Recipe.OrdinaryData`, `OAI.SKGapCutoff.Recipe.SmallBound` and `OAI.SKGap.Noncrossing.Primary.SourceTree` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.LocalConstants` and `OAI.SKGapCutoff.Recipe.LocalConstants.startedSourceCost` (definitions bundle `OAIQ072A001` of this split); `OAI.SKGapCutoff.Recipe.LocalOrdinaryInput`, `OAI.SKGapCutoff.Recipe.TraceControl` and `OAI.SKGapCutoff.Recipe.OrdinaryData.startedNodeSourceError` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ072A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace LocalOrdinaryInput
variable {D : OrdinaryData n ι κ σ} {T : ι→SourceTree (Fin n→ℝ)}
variable {x : Spin n} {N : ℕ} {c : LocalConstants} {w y : VectorFields n} {B : ℝ}
variable (h : LocalOrdinaryInput D T x N c) (hB : 0≤B) (hw₀ : SmallBound w x B) (hy₀ : SmallBound y x B)
include h hB hw₀ hy₀

lemma started_source_control_s2 (a : ℕ) (ha : a≤N) :
    TraceControl (D.startedNodeSourceError w y T x a) (c.startedSourceCost D.j (Fintype.card ι) (Fintype.card σ) B a) := by
  sorry

end LocalOrdinaryInput
end SKGapCutoff.Recipe

end
end

end OAI
end
