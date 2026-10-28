-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_source_all_levels_eventually
-- name    : OAI.TraceReconstruction.source_all_levels_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:52:11.949499+00:00
-- url     : https://prove2.me/theorems/2b06621d-2c3d-41e7-8432-bf28c8ceda08
-- title:
--   OAI.TraceReconstruction.source_all_levels_eventually: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.source_all_levels_eventually` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open Filter`, `open scoped Topology Classical`):
--
--   ```lean
--   theorem source_all_levels_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
--       (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
--       (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
--       (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
--       ∀ᶠt in atTop,∀i ≤ sourceDepth B ζ ((q t)^3*Real.log (n t)),
--         Nonempty (SourceLevelPair B (sourceDepth B ζ ((q t)^3*Real.log (n t)))
--           (n t) (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩ i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.SourceLevelPair` (definitions bundle `OAIQ9Tr000` of this split); `OAI.TraceReconstruction.sourceDepth` (definitions bundle `OAIQ9Tr001` of this split).
--
--   **Used by.** The proofs of `OAI.TraceReconstruction.quantitative_sample_lower_bound` and `OAI.TraceReconstruction.superpolynomial_one_trace` of this split import it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean (declaration OAI.TraceReconstruction.source_all_levels_eventually)

import Mathlib
import Definitions.Def_OAIQ9Tr000
import Definitions.Def_OAIQ9Tr001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem source_all_levels_eventually (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i ≤ sourceDepth B ζ ((q t)^3*Real.log (n t)),
      Nonempty (SourceLevelPair B (sourceDepth B ζ ((q t)^3*Real.log (n t)))
        (n t) (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩ i) := by
  sorry

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end
