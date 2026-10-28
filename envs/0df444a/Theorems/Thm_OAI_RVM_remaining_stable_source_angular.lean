-- Prove2me | Theorems.Thm_OAI_RVM_remaining_stable_source_angular
-- name    : OAI.RVM.remaining_stable_source_angular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:28:34.806407+00:00
-- url     : https://prove2.me/theorems/827ef5ac-3dce-4704-884a-ea51cb83e680
-- title:
--   OAI.RVM.remaining_stable_source_angular: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.remaining_stable_source_angular` of [lean/OAI/Analysis/VlasovMaxwell/Population/TransportRemainder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/TransportRemainder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory _root_.Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma remaining_stable_source_angular {I P C M A p w φ K κ g b : ℝ}
--       (hI : 0<I) (hP : 0<P) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
--       (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hK : 0<K) (hκ : 0<κ)
--       (hg : 0≤g) (hb : 0≤b)
--       (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
--       (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
--       (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
--       let B := 2*Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
--         (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
--       ∑i∈Sθ,∑j∈Sσ i,
--         Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P C M A p w (cappedRepresentative j)/2)))*
--           relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
--             (g*(φ/(cappedRepresentative i)^2)+b) ≤
--       g*(2*remainingGoodConstant K κ 0*Real.sqrt φ+B*remainingGoodConstant K κ (1/2))+
--       b*(2*remainingMagneticConstant K κ 0+B*remainingMagneticConstant K κ (1/2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.cappedRepresentative`, `OAI.RVM.relativeSourceAngle`, `OAI.RVM.remainingGoodConstant`, `OAI.RVM.remainingMagneticConstant` and `OAI.RVM.stabilityLength` (definitions bundle `OAIQ073V000` of this split).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direct_source_shared_short_angles_expanded` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/TransportRemainder.lean (declaration OAI.RVM.remaining_stable_source_angular)

import Mathlib
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

lemma remaining_stable_source_angular {I P C M A p w φ K κ g b : ℝ}
    (hI : 0<I) (hP : 0<P) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hK : 0<K) (hκ : 0<κ)
    (hg : 0≤g) (hb : 0≤b)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    let B := 2*Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
      (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
    ∑i∈Sθ,∑j∈Sσ i,
      Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P C M A p w (cappedRepresentative j)/2)))*
        relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
          (g*(φ/(cappedRepresentative i)^2)+b) ≤
    g*(2*remainingGoodConstant K κ 0*Real.sqrt φ+B*remainingGoodConstant K κ (1/2))+
    b*(2*remainingMagneticConstant K κ 0+B*remainingMagneticConstant K κ (1/2)) := by
  sorry

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

end RVM

end

end OAI
end
