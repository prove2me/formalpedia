-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryDyadic_lookup_draw_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:57:49.691202+00:00
-- url     : https://prove2.me/theorems/f8314759-eca3-4ea1-8882-f33a4ade5522
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/DyadicLookup.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/DyadicLookup.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic`, with `open WordOperations WordList BinaryArithmetic`):
--
--   ```lean
--   lemma lookup_draw_s238r {A : Type*} (code : A→List Bool) (p : A→ℚ) (d : A) (as : List A)
--       (ha : as[0]?=some d) (b : ℕ) (s : Fin b→Bool) :
--       Lookup.run (pairBits (run (pack b 0 (as.map p) (List.ofFn s)),encode (as.map code)))=
--         code (Dyadic.Canonical.draw (fun a=>(p a:ℝ)) b d as s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` and `OAI.MetricKMedianRecovery.BitMachine.WordList.Lookup.run` (definitions bundle `Q238L006` of this split); `OAI.MetricKMedianRecovery.Dyadic.Canonical.draw` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.pack` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.run` (definitions bundle `Q238L034` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/DyadicLookup.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
lemma lookup_draw_s238r {A : Type*} (code : A→List Bool) (p : A→ℚ) (d : A) (as : List A)
    (ha : as[0]?=some d) (b : ℕ) (s : Fin b→Bool) :
    Lookup.run (pairBits (run (pack b 0 (as.map p) (List.ofFn s)),encode (as.map code)))=
      code (Dyadic.Canonical.draw (fun a=>(p a:ℝ)) b d as s) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end
