-- Prove2me | Theorems.Thm_OAI_RVM_family_bounded_classical_prefix
-- name    : OAI.RVM.family_bounded_classical_prefix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:25:24.530103+00:00
-- url     : https://prove2.me/theorems/b604d92a-4f16-4689-86ea-173db4303781
-- title:
--   OAI.RVM.family_bounded_classical_prefix: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.family_bounded_classical_prefix` of [lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem family_bounded_classical_prefix {ι : Type*} {d : ι → Datum}
--       (hd : ∀ j, Admissible (d j)) {A R P L J : ℝ}
--       (hA : 0≤A) (hR : 0≤R) (hP : 0≤P) (hL : 0≤L) (hJ : 0≤J)
--       (hf : ∀ j z, |(d j).f₀ z|≤A)
--       (hrp : ∀ j (z : Phase), (d j).f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P)
--       (hl : ∀ j z w, |(d j).f₀ z-(d j).f₀ w|≤L*‖z-w‖)
--       (hEj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).E₀ x‖≤J)
--       (hBj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).B₀ x‖≤J) :
--       ∃ T : ℝ, 0<T ∧ ∀ j, ∃ s : Solution, BoundedClassicalPrefix (d j) s T
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.BoundedClassicalPrefix` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.bounded_momentum_uniform_restart` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean (declaration OAI.RVM.family_bounded_classical_prefix)

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

theorem family_bounded_classical_prefix {ι : Type*} {d : ι → Datum}
    (hd : ∀ j, Admissible (d j)) {A R P L J : ℝ}
    (hA : 0≤A) (hR : 0≤R) (hP : 0≤P) (hL : 0≤L) (hJ : 0≤J)
    (hf : ∀ j z, |(d j).f₀ z|≤A)
    (hrp : ∀ j (z : Phase), (d j).f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P)
    (hl : ∀ j z w, |(d j).f₀ z-(d j).f₀ w|≤L*‖z-w‖)
    (hEj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).E₀ x‖≤J)
    (hBj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).B₀ x‖≤J) :
    ∃ T : ℝ, 0<T ∧ ∀ j, ∃ s : Solution, BoundedClassicalPrefix (d j) s T := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
