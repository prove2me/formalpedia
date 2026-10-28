-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_magnetic_small_uniform
-- name    : OAI.RVM.Admissible.magnetic_small_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:09:08.720984+00:00
-- url     : https://prove2.me/theorems/3b277eac-bfd4-46dc-b4e0-7a4f502abcd5
-- title:
--   OAI.RVM.Admissible.magnetic_small_uniform: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.magnetic_small_uniform` of [lean/OAI/Analysis/VlasovMaxwell/Population/MagneticEstimates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/MagneticEstimates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.magnetic_small_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
--       ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (a b I w : ℝ),
--         zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
--         (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
--           1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
--         (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
--           if cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
--             representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
--           ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.representativeMagneticCost` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.bulk_source_uniform`, `OAI.RVM.Admissible.small_source_absolute_uniform` and `OAI.RVM.Admissible.unselected_small_source_uniform` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/MagneticEstimates.lean (declaration OAI.RVM.Admissible.magnetic_small_uniform)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.magnetic_small_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
          representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end
