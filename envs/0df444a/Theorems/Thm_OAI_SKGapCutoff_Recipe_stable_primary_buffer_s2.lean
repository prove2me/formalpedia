-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_stable_primary_buffer_s2
-- name    : OAI.SKGapCutoff.Recipe.stable_primary_buffer_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:53:20.567766+00:00
-- url     : https://prove2.me/theorems/92ce718f-c404-485e-a0c2-fb2d9a91e674
-- title:
--   OAI.SKGapCutoff.Recipe.stable_primary_buffer_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix`, `open SKGap Primary Static SKGap.ObservationBridge SKGap.Stein`):
--
--   ```lean
--   theorem stable_primary_buffer_s2 (hn : 0<n) {j K A ε c r₀ R ρ : ℝ}
--       (hj : 0≤j) (hK : 0≤K) (hA : 1≤A) (hc : 0 < c) (hr₀ : 0 < r₀) (hρ : 0≤ρ)
--       (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
--       (hbuffer : (K+4*j)*ρ < r₀)
--       (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ≤R)
--       (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ)≤ε)
--       (J : Interaction n) (hJ : J.IsSymm) (h : Fin n→ℝ)
--       (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v)
--       (hbad : ¬rootBad j A ε c r₀ J h) :
--       ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
--         ∀k x,
--         vectorNorm (Primary.residual j J h k x)≤ρ*Real.sqrt (n:ℝ)→
--         vectorNorm (Primary.residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ)→
--         LiteralStableAt J j (fld j J h (k+1)) (mag j J h (k+1))
--           (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r R
--           ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ) c x
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.Field`, `OAI.SKGap.overlap`, `OAI.SKGap.rootBad`, `OAI.SKGap.tapField`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.Primary.fld`, `OAI.SKGapCutoff.Primary.mag`, `OAI.SKGapCutoff.Primary.onsager`, `OAI.SKGapCutoff.Primary.residual` and `OAI.SKGapCutoff.Recipe.vectorNorm` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.LiteralStableAt` (definitions bundle `OAIQ072A002` of this split).
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
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap Primary Static SKGap.ObservationBridge SKGap.Stein
variable {n : ℕ}

theorem stable_primary_buffer_s2 (hn : 0<n) {j K A ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hA : 1≤A) (hc : 0 < c) (hr₀ : 0 < r₀) (hρ : 0≤ρ)
    (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hbuffer : (K+4*j)*ρ < r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ)≤ε)
    (J : Interaction n) (hJ : J.IsSymm) (h : Fin n→ℝ)
    (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v)
    (hbad : ¬rootBad j A ε c r₀ J h) :
    ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀k x,
      vectorNorm (Primary.residual j J h k x)≤ρ*Real.sqrt (n:ℝ)→
      vectorNorm (Primary.residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ)→
      LiteralStableAt J j (fld j J h (k+1)) (mag j J h (k+1))
        (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r R
        ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ) c x := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
