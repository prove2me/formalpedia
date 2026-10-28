-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_representative_receiver_envelope
-- name    : OAI.RVM.Admissible.representative_receiver_envelope
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:10:41.798081+00:00
-- url     : https://prove2.me/theorems/c1d72e1c-928f-4aaa-b990-1e98b952f2f2
-- title:
--   OAI.RVM.Admissible.representative_receiver_envelope: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.representative_receiver_envelope` of [lean/OAI/Analysis/VlasovMaxwell/Population/ReceiverWeights.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/ReceiverWeights.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.representative_receiver_envelope {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
--       ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (k : Fin 4→ℕ) (a b w : ℝ) (g : ℝ→ℝ≥0∞),
--         0≤a → b≤T → 0<w → Measurable g → (∀t,g t≠⊤) →
--         let p := sourceRepresentative (k 0)
--         let θ := cappedRepresentative (k 1)
--         let φ := cappedRepresentative (k 2)
--         let h := cappedRepresentative (k 3)
--         representativeReceiverCost s F zX w k a b g≤
--           ENNReal.ofReal (C*receiverCoefficient w p θ φ h)*(∫⁻t in Icc a b,g t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.receiverCoefficient`, `OAI.RVM.representativeReceiverCost` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase` and `OAI.RVM.Solution` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.bulk_remainder_uniform`, `OAI.RVM.Admissible.bulk_selected_family_uniform` and `OAI.RVM.Admissible.time_weight_bin_near` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/ReceiverWeights.lean (declaration OAI.RVM.Admissible.representative_receiver_envelope)

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

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

lemma Admissible.representative_receiver_envelope {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b w : ℝ) (g : ℝ→ℝ≥0∞),
      0≤a → b≤T → 0<w → Measurable g → (∀t,g t≠⊤) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      representativeReceiverCost s F zX w k a b g≤
        ENNReal.ofReal (C*receiverCoefficient w p θ φ h)*(∫⁻t in Icc a b,g t) := by
  sorry

open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

end RVM

end

end OAI
end
