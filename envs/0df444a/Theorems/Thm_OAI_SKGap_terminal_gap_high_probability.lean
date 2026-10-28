-- Prove2me | Theorems.Thm_OAI_SKGap_terminal_gap_high_probability
-- name    : OAI.SKGap.terminal_gap_high_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:25:15.641466+00:00
-- url     : https://prove2.me/theorems/042f74d1-aec2-4ffc-8553-8df55d08c53d
-- title:
--   OAI.SKGap.terminal_gap_high_probability: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.terminal_gap_high_probability` of [lean/OAI/Probability/SKGap/Terminal/TerminalChannel.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Terminal/TerminalChannel.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open MeasureTheory ProbabilityTheory Real Set Filter`, `open scoped BigOperators Topology Matrix.Norms.L2Operator`):
--
--   ```lean
--   theorem terminal_gap_high_probability {β : ℝ} (hβ : 0 < β) :
--       ∃ T a : ℝ,0 < T ∧ 0 < a ∧ ∃ Ω : (n : ℕ)→Set (Disorder n),
--         (∀ n,MeasurableSet (Ω n)) ∧
--         Tendsto (fun n=>(disorderLaw β n).real (Ω n)) atTop (𝓝 1) ∧
--         ∀ (n : ℕ) (g : Disorder n),g ∈ Ω n →
--           (gaussianChannelLaw g T).real {z | ¬∀ f : Spin n→ℝ,
--             variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f} ≤ exp (-a*(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.gaussianChannelLaw` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGap.Disorder`, `OAI.SKGap.Edge`, `OAI.SKGap.Spin`, `OAI.SKGap.dirichlet`, `OAI.SKGap.disorderLaw` and `OAI.SKGap.variance` (the published bundle `Def_SKHighTemperature`).
--
--   **Used by.** The proof of `OAI.SKGap.sk_main` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Terminal/TerminalChannel.lean (declaration OAI.SKGap.terminal_gap_high_probability)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A000

section

attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator
variable {n : ℕ}

theorem terminal_gap_high_probability {β : ℝ} (hβ : 0 < β) :
    ∃ T a : ℝ,0 < T ∧ 0 < a ∧ ∃ Ω : (n : ℕ)→Set (Disorder n),
      (∀ n,MeasurableSet (Ω n)) ∧
      Tendsto (fun n=>(disorderLaw β n).real (Ω n)) atTop (𝓝 1) ∧
      ∀ (n : ℕ) (g : Disorder n),g ∈ Ω n →
        (gaussianChannelLaw g T).real {z | ¬∀ f : Spin n→ℝ,
          variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f} ≤ exp (-a*(n:ℝ)) := by
  sorry
end SKGap

end
end

end OAI
end
