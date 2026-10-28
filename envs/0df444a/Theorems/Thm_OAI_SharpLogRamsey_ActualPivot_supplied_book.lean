-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_ActualPivot_supplied_book
-- name    : OAI.SharpLogRamsey.ActualPivot.supplied_book
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:22:32.213281+00:00
-- url     : https://prove2.me/theorems/38c75a70-4a69-4408-8f52-7a4c1008b77a
-- title:
--   OAI.SharpLogRamsey.ActualPivot.supplied_book: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.ActualPivot.supplied_book` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/SuppliedBook.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/SuppliedBook.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.ActualPivot`, with `open Real Filter SourceScales`, `open scoped Topology`):
--
--   ```lean
--   theorem supplied_book (i : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
--       ∀ η : ℝ, 0 < η → ∀ᶠ σ : ℝ in atTop,
--       ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ = (q:ℝ) →
--       ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
--       Module.finrank (ZMod q) V = i+4 → ∀ D R, Admissible σ η D R →
--       let b := 16*scaleKstar σ η D
--       let τ := σ^(-100*beta η)
--       0 ≤ b ∧ 4 ≤ scaleP σ η D R ∧ b+log 1000000 ≤ scaleP σ η D R ∧
--       0 ≤ τ ∧ τ ≤ 1/40000 ∧
--       Nonempty (Book (K:=ZMod q) (V:=V) (Nat.card (ZMod q)) b τ
--         (scaleP σ η D R) H ((i+1)+3))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualPivot.Book`, `OAI.SharpLogRamsey.SourceScales.Admissible`, `OAI.SharpLogRamsey.SourceScales.beta`, `OAI.SharpLogRamsey.SourceScales.scaleKstar` and `OAI.SharpLogRamsey.SourceScales.scaleP` (definitions bundle `OAIQ045S000` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.Marking.eventually_class_step` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/SuppliedBook.lean (declaration OAI.SharpLogRamsey.ActualPivot.supplied_book)

import Mathlib
import Definitions.Def_OAIQ045S000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter SourceScales
open scoped Topology
noncomputable section

theorem supplied_book (i : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ σ : ℝ in atTop,
    ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ = (q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V = i+4 → ∀ D R, Admissible σ η D R →
    let b := 16*scaleKstar σ η D
    let τ := σ^(-100*beta η)
    0 ≤ b ∧ 4 ≤ scaleP σ η D R ∧ b+log 1000000 ≤ scaleP σ η D R ∧
    0 ≤ τ ∧ τ ≤ 1/40000 ∧
    Nonempty (Book (K:=ZMod q) (V:=V) (Nat.card (ZMod q)) b τ
      (scaleP σ η D R) H ((i+1)+3)) := by
  sorry
end
end SharpLogRamsey.ActualPivot

end

end OAI
end
