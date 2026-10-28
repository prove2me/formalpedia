-- Prove2me | Theorems.Thm_OAI_RVM_exists_picard_field_limit
-- name    : OAI.RVM.exists_picard_field_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:24:29.381595+00:00
-- url     : https://prove2.me/theorems/e10f5a7b-1928-4391-85cc-8bd235558306
-- title:
--   OAI.RVM.exists_picard_field_limit: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.exists_picard_field_limit` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem exists_picard_field_limit {d : Datum} (hd : Admissible d) :
--       ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
--         ∃ (S : ℕ → Solution) (E B : Field), S 0=datumBoundarySolution d ∧
--           (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
--           (∀ n, FieldControl T L N (S n).E (S n).B) ∧
--           (∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
--             LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
--           (∀ n, ∀ t∈Icc 0 T, ∀ x,
--             ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
--             ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) ∧
--           TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T} ∧
--           TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T} ∧
--           ContinuousOn E {p | p.1∈Icc 0 T} ∧ ContinuousOn B {p | p.1∈Icc 0 T} ∧
--           FieldControl T L N E B
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.FieldControl`, `OAI.RVM.LocalParticleBound`, `OAI.RVM.PhaseParticleLip`, `OAI.RVM.PicardRegular`, `OAI.RVM.TransportFor` and `OAI.RVM.datumBoundarySolution` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Field`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.exists_local_spatially_smooth_bounded_classical` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean (declaration OAI.RVM.exists_picard_field_limit)

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
open scoped Topology ContDiff

namespace RVM

theorem exists_picard_field_limit {d : Datum} (hd : Admissible d) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∃ (S : ℕ → Solution) (E B : Field), S 0=datumBoundarySolution d ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        (∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) ∧
        TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T} ∧
        TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T} ∧
        ContinuousOn E {p | p.1∈Icc 0 T} ∧ ContinuousOn B {p | p.1∈Icc 0 T} ∧
        FieldControl T L N E B := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
