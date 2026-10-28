-- Prove2me | Theorems.Thm_OAI_SKGap_ObservationBridge_annealed_fixed_time_root_stability
-- name    : OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:17.260128+00:00
-- url     : https://prove2.me/theorems/bb814fd9-9721-46cf-9eb7-fbc1108e30a0
-- title:
--   OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability` of [lean/OAI/Probability/SKGap/Stability/FixedTimeAnnealed.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/FixedTimeAnnealed.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap.ObservationBridge`, with `open Matrix Real Set MeasureTheory ProbabilityTheory`, `open scoped BigOperators ENNReal NNReal`):
--
--   ```lean
--   theorem annealed_fixed_time_root_stability {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
--       ∃ A K ε c ρ a : ℝ, 1<A ∧ 2*β<K ∧ β*A<1 ∧
--         0<ε ∧ 0 < c ∧ 0<ρ ∧ 0<a ∧ ∃ N : ℕ, 0<N ∧ ∀ n≥N, ∀ t∈Icc 0 T,
--         (∫⁻ J : Disorder n,
--           ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
--             fixedTimeFailureENN (β^2) A K ε c ρ t J ∂disorderLaw β n) ≤
--           ENNReal.ofReal (exp (-a*(n:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.ObservationBridge.fixedTimeFailureENN` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGap.Disorder`, `OAI.SKGap.Edge`, `OAI.SKGap.disorderLaw` and `OAI.SKGap.partition` (the published bundle `Def_SKHighTemperature`).
--
--   **Used by.** The proof of `OAI.SKGap.FullMain.quenched_grid_root_stability` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/FixedTimeAnnealed.lean (declaration OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}

theorem annealed_fixed_time_root_stability {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
    ∃ A K ε c ρ a : ℝ, 1<A ∧ 2*β<K ∧ β*A<1 ∧
      0<ε ∧ 0 < c ∧ 0<ρ ∧ 0<a ∧ ∃ N : ℕ, 0<N ∧ ∀ n≥N, ∀ t∈Icc 0 T,
      (∫⁻ J : Disorder n,
        ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
          fixedTimeFailureENN (β^2) A K ε c ρ t J ∂disorderLaw β n) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  sorry
end SKGap.ObservationBridge

end
end

end OAI
end
