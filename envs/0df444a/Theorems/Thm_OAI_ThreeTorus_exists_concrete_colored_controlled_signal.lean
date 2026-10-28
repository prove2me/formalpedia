-- Prove2me | Theorems.Thm_OAI_ThreeTorus_exists_concrete_colored_controlled_signal
-- name    : OAI.ThreeTorus.exists_concrete_colored_controlled_signal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:04:48.975782+00:00
-- url     : https://prove2.me/theorems/387355c8-3a20-4733-baa9-184ffd9b71fe
-- title:
--   OAI.ThreeTorus.exists_concrete_colored_controlled_signal: intermediate lemma from OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThreeTorus.simple_lebesgue_spectrum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, OpenAI Math Release, September 23, 2026, result family 144, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThreeTorus.exists_concrete_colored_controlled_signal` of [lean/OAI/Dynamics/ThreeTorus/ThreeTorus/ControlledBlocks.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/ControlledBlocks.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThreeTorus`, with `open Set Function Filter MeasureTheory`, `open scoped Topology BigOperators`):
--
--   ```lean
--   theorem exists_concrete_colored_controlled_signal {b D : ℝ} (hb : 0 < b) (hbD : b < D)
--       {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
--       (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
--       (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
--       ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
--         ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
--         (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
--         ColoredSignalControlledRealizes b D d γ (refreshedStrength (signalPrimeProduct L) γ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThreeTorus.ColoredSignalControlledRealizes`, `OAI.ThreeTorus.instNeZeroNatSignalPrimeProduct`, `OAI.ThreeTorus.refreshedStrength` and `OAI.ThreeTorus.signalPrimeProduct` (definitions bundle `OAIQ13Tt000` of this split).
--
--   **Used by.** The proof of `OAI.ThreeTorus.actual_controlled_density_prediction` of this split imports it.
-- source:
--   OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 144; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/ControlledBlocks.lean (declaration OAI.ThreeTorus.exists_concrete_colored_controlled_signal)

import Mathlib
import Definitions.Def_OAIQ13Tt000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

theorem exists_concrete_colored_controlled_signal {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ColoredSignalControlledRealizes b D d γ (refreshedStrength (signalPrimeProduct L) γ) := by
  sorry

end ThreeTorus
end
end

end OAI
end
