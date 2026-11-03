-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_retainedFourReal_outer_trace_s50
-- name    : OAI.Laughlin.Spin.retainedFourReal_outer_trace_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T21:01:26.800545+00:00
-- url     : https://prove2.me/theorems/93ee8431-5b15-418e-aaed-fdee7fd131a7
-- title:
--   OAI.Laughlin.Spin.retainedFourReal_outer_trace_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.retainedFourReal_outer_trace` of [lean/OAI/Analysis/Laughlin/FourBody/TraceReadout.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/TraceReadout.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem retainedFourReal_outer_trace_s50 (Q D T p j k q l i : ℕ) (hQ : D+2 ≤ Q)
--       (hTQ : T+2 ≤ Q) (r s : OddPairLabel D) (hp : p+j+k=T) (hq : q+l+i=T) :
--       Matrix.trace ((retainedFourReal Q D hQ r)ᵀ *
--         realOuter (fourSignedUnit Q p j k) (fourSignedUnit Q q l i) * retainedFourReal Q D hQ s) =
--         if D ≤ T then fourBodyCoefficient Q (oddPairDeficit r) D T p j k *
--           fourBodyCoefficient Q (oddPairDeficit s) D T q l i else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Spin.OddPairLabel` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.fourSpinWeight` and `OAI.Laughlin.Spin.realOuter` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Spin.fourBodyCoefficient` (definitions bundle `OAIQ050L010` of this split); `OAI.Laughlin.Spin.FourWedgeIndex`, `OAI.Laughlin.Spin.WedgePairIndex`, `OAI.Laughlin.Spin.fourSignedUnit` and `OAI.Laughlin.Spin.oddPairDeficit` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Spin.retainedFourReal` (definitions bundle `OAIQ050L021` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Spin.physical_fourBody_haar_multiplicity_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/TraceReadout.lean (declaration OAI.Laughlin.Spin.retainedFourReal_outer_trace)

import Mathlib
import Definitions.Def_OAIQ050L021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem retainedFourReal_outer_trace_s50 (Q D T p j k q l i : ℕ) (hQ : D+2 ≤ Q)
    (hTQ : T+2 ≤ Q) (r s : OddPairLabel D) (hp : p+j+k=T) (hq : q+l+i=T) :
    Matrix.trace ((retainedFourReal Q D hQ r)ᵀ *
      realOuter (fourSignedUnit Q p j k) (fourSignedUnit Q q l i) * retainedFourReal Q D hQ s) =
      if D ≤ T then fourBodyCoefficient Q (oddPairDeficit r) D T p j k *
        fourBodyCoefficient Q (oddPairDeficit s) D T q l i else 0 := by
  sorry

end Laughlin.Spin

end OAI
end
