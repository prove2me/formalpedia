-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_source_initial_level_eventually
-- name    : OAI.TraceReconstruction.source_initial_level_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:52:05.092383+00:00
-- url     : https://prove2.me/theorems/ecbd3283-c69a-4b98-9446-3a98d835f37b
-- title:
--   OAI.TraceReconstruction.source_initial_level_eventually: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.source_initial_level_eventually` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialRates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialRates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open Filter`, `open scoped Topology Classical`):
--
--   ```lean
--   theorem source_initial_level_eventually {N q n A : ℕ→ℝ} {k : ℕ→ℕ}
--       (hN : Tendsto N atTop atTop) (hn : Tendsto n atTop atTop)
--       (hA : ∀ᶠt in atTop,1 ≤ A t) (hq : ∀t,q t ∈ Set.Ioc 0 (1/2:ℝ))
--       (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
--       (hk : PowerRate N (fun t=>(k t:ℝ)) 0) (hk1 : ∀ᶠt in atTop,1 ≤ k t)
--       (hmoment : ∀ᶠt in atTop,10^6*A t*Real.log (n t) ≤ (k t:ℝ)*Real.log (N t))
--       (hscale : ∀ᶠt in atTop,N t ≤ n t) :
--       ∀ᶠt in atTop,Nonempty (ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩
--         (N t) ((n t)^(-100*A t)) (11/5) (initialOverlapLower (q t))
--         ((sourceOverlapConstant (q t))^2) 0 (k t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.ConcreteLevelPair`, `OAI.TraceReconstruction.PowerRate`, `OAI.TraceReconstruction.initialOverlapLower` and `OAI.TraceReconstruction.sourceOverlapConstant` (definitions bundle `OAIQ9Tr000` of this split).
--
--   **Used by.** The proof of `OAI.TraceReconstruction.source_all_levels_eventually` of this split imports it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialRates.lean (declaration OAI.TraceReconstruction.source_initial_level_eventually)

import Mathlib
import Definitions.Def_OAIQ9Tr000

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

noncomputable section

noncomputable section

noncomputable section

noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem source_initial_level_eventually {N q n A : ℕ→ℝ} {k : ℕ→ℕ}
    (hN : Tendsto N atTop atTop) (hn : Tendsto n atTop atTop)
    (hA : ∀ᶠt in atTop,1 ≤ A t) (hq : ∀t,q t ∈ Set.Ioc 0 (1/2:ℝ))
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) (hk1 : ∀ᶠt in atTop,1 ≤ k t)
    (hmoment : ∀ᶠt in atTop,10^6*A t*Real.log (n t) ≤ (k t:ℝ)*Real.log (N t))
    (hscale : ∀ᶠt in atTop,N t ≤ n t) :
    ∀ᶠt in atTop,Nonempty (ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩
      (N t) ((n t)^(-100*A t)) (11/5) (initialOverlapLower (q t))
      ((sourceOverlapConstant (q t))^2) 0 (k t)) := by
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
end
end
end
end

end OAI
end
