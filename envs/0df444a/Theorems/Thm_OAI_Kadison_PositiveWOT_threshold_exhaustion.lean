-- Prove2me | Theorems.Thm_OAI_Kadison_PositiveWOT_threshold_exhaustion
-- name    : OAI.Kadison.PositiveWOT.threshold_exhaustion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:23:07.311654+00:00
-- url     : https://prove2.me/theorems/3a8728b3-2f0e-410f-8a1b-2ffcd6fa056d
-- title:
--   OAI.Kadison.PositiveWOT.threshold_exhaustion: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PositiveWOT`, with `open Filter`, `open scoped ComplexOrder InnerProductSpace Topology`):
--
--   ```lean
--   theorem threshold_exhaustion (M : VonNeumannAlgebra H) {B : H →L[ℂ] H}
--       (hBM : B∈M) (hB : 0≤B) (hi : Function.Injective B) :
--       Monotone (fun n : ℕ => threshold B (1/((n:ℝ)+1))) ∧
--         ∀ x,Tendsto (fun n : ℕ => threshold B (1/((n:ℝ)+1)) x) atTop (𝓝 x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PositiveWOT.threshold` (definitions bundle `OAIQ039C040` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.PositiveWOT.positive_strong_null` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C040

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem threshold_exhaustion (M : VonNeumannAlgebra H) {B : H →L[ℂ] H}
    (hBM : B∈M) (hB : 0≤B) (hi : Function.Injective B) :
    Monotone (fun n : ℕ => threshold B (1/((n:ℝ)+1))) ∧
      ∀ x,Tendsto (fun n : ℕ => threshold B (1/((n:ℝ)+1)) x) atTop (𝓝 x) := by
  sorry

end Kadison.PositiveWOT

end

end
end

end OAI
end
