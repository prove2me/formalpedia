-- Prove2me | Theorems.Thm_OAI_SK_Analytic_signed_small_scale
-- name    : OAI.SK.Analytic.signed_small_scale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:52:37.306683+00:00
-- url     : https://prove2.me/theorems/72a2cc63-abef-4ea0-b0a8-a9977d5692be
-- title:
--   OAI.SK.Analytic.signed_small_scale: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.signed_small_scale` of [lean/OAI/Probability/SKBarriers/SKBarriers/Locking/LockingScales.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/LockingScales.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators Topology`, `open Classical MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--    theorem signed_small_scale {β h : ℝ} (hβ : 0<β) (hh : 0<h) (hh1 : h≤1) {e : ℝ} (he : 0<e) :
--       ∃b : ℝ,0<b ∧ b<e ∧ ∀ᶠ n : ℕ in atTop,
--         (∫J,replicaGibbsMass β J (signedLockingSet n h b) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((9:ℝ)/10))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.signedLockingSet` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.replicaGibbsMass` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Disorder`, `OAI.SK.Edge` and `OAI.SK.disorderLaw` (the published bundle `Def_SKBarriers`).
--
--   **Used by.** The proof of `OAI.SK.main` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/LockingScales.lean (declaration OAI.SK.Analytic.signed_small_scale)

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S002
import Definitions.Def_OAIQ036S003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem signed_small_scale {β h : ℝ} (hβ : 0<β) (hh : 0<h) (hh1 : h≤1) {e : ℝ} (he : 0<e) :
    ∃b : ℝ,0<b ∧ b<e ∧ ∀ᶠ n : ℕ in atTop,
      (∫J,replicaGibbsMass β J (signedLockingSet n h b) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((9:ℝ)/10)) := by
  sorry

end SK.Analytic

end
end

end OAI
end
