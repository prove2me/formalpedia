-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_fourWeightSlice_sum_s50
-- name    : OAI.Laughlin.Spin.fourWeightSlice_sum_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:46:29.0472+00:00
-- url     : https://prove2.me/theorems/52019b26-8729-4c21-9d28-49a6720d5d02
-- title:
--   OAI.Laughlin.Spin.fourWeightSlice_sum_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.fourWeightSlice_sum` of [lean/OAI/Analysis/Laughlin/FourBody/WeightSlice.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/WeightSlice.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem fourWeightSlice_sum_s50 {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hQ : D+2 ≤ Q)
--       (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
--       (∑ p : Fin (2*Q-2+1), ∑ i : WedgePairIndex Q,
--         if p.val+i.val.1.val+i.val.2.val=D then f p.val i.val.1 i.val.2 else 0) =
--         ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Spin.LocalFourIndex` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.WedgePairIndex` (definitions bundle `OAIQ050L012` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physicalFourCopyEnd_column_s50` and `OAI.Laughlin.Spin.source_fourBody_local_orthonormal_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/WeightSlice.lean (declaration OAI.Laughlin.Spin.fourWeightSlice_sum)

import Mathlib
import Definitions.Def_OAIQ050L012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem fourWeightSlice_sum_s50 {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hQ : D+2 ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (2*Q-2+1), ∑ i : WedgePairIndex Q,
      if p.val+i.val.1.val+i.val.2.val=D then f p.val i.val.1 i.val.2 else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  sorry

end Laughlin.Spin

end OAI
end
