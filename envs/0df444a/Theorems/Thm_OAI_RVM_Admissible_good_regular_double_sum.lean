-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_good_regular_double_sum
-- name    : OAI.RVM.Admissible.good_regular_double_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:08:20.507118+00:00
-- url     : https://prove2.me/theorems/0962e305-75db-44e1-82ec-a00e953c52ed
-- title:
--   OAI.RVM.Admissible.good_regular_double_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.good_regular_double_sum` of [lean/OAI/Analysis/VlasovMaxwell/Population/GoodSharedEstimates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/GoodSharedEstimates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory _root_.Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.good_regular_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
--       ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,0<M → 0≤A → 0<P →
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
--         zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
--         sourceRepresentative np≤P → I≤(w/P)^2 →
--         (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         (∑'nt : ℕ,∑'nr : ℕ,if 1/sourceRepresentative np ≤ cappedRepresentative nt ∧
--           cappedRepresentative nt ≤ cappedRepresentative nf/16 then
--             representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
--           ENNReal.ofReal (C*Real.sqrt w*Real.sqrt I*representativeSharedRadius s F zX P M A w a b I (np,nf)*
--             sourceRepresentative np*cappedRepresentative nf)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.representativeRegularGoodCost`, `OAI.RVM.representativeSharedRadius` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.small_good_uniform` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/GoodSharedEstimates.lean (declaration OAI.RVM.Admissible.good_regular_double_sum)

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

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

lemma Admissible.good_regular_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      sourceRepresentative np≤P → I≤(w/P)^2 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'nt : ℕ,∑'nr : ℕ,if 1/sourceRepresentative np ≤ cappedRepresentative nt ∧
        cappedRepresentative nt ≤ cappedRepresentative nf/16 then
          representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*Real.sqrt w*Real.sqrt I*representativeSharedRadius s F zX P M A w a b I (np,nf)*
          sourceRepresentative np*cappedRepresentative nf) := by
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
