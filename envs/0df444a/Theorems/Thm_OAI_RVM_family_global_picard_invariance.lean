-- Prove2me | Theorems.Thm_OAI_RVM_family_global_picard_invariance
-- name    : OAI.RVM.family_global_picard_invariance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:25:24.356488+00:00
-- url     : https://prove2.me/theorems/8a306c6d-beb4-4831-b053-597092513989
-- title:
--   OAI.RVM.family_global_picard_invariance: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.family_global_picard_invariance` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/StrongLocalExistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/StrongLocalExistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem family_global_picard_invariance {ι : Type*} {d : ι → Datum} (_ : ∀ i, Admissible (d i))
--       {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
--       (hD : 0≤D) (_ : 0≤D₀) (_ : 0≤A₁)
--       (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
--       ∃ T A R P L : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧
--         (∀ i, GlobalFieldBound T L (fun p : ℝ × Vec => (d i).E₀ p.2) (fun p : ℝ × Vec => (d i).B₀ p.2) ∧
--         ∀ U : ℝ, 0≤U → U≤T → ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → GlobalFieldBound U L E B →
--           ∀ s : Solution, PicardRegular (d i) s → TransportFor s E B →
--             LocalParticleBound U A R P s.f ∧ GlobalFieldBound U L s.E s.B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.DatumRestartControl`, `OAI.RVM.GlobalFieldBound`, `OAI.RVM.LocalParticleBound`, `OAI.RVM.PicardRegular` and `OAI.RVM.TransportFor` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Field`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.family_picard_field_limit` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/StrongLocalExistence.lean (declaration OAI.RVM.family_global_picard_invariance)

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

theorem family_global_picard_invariance {ι : Type*} {d : ι → Datum} (_ : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (_ : 0≤D₀) (_ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧
      (∀ i, GlobalFieldBound T L (fun p : ℝ × Vec => (d i).E₀ p.2) (fun p : ℝ × Vec => (d i).B₀ p.2) ∧
      ∀ U : ℝ, 0≤U → U≤T → ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → GlobalFieldBound U L E B →
        ∀ s : Solution, PicardRegular (d i) s → TransportFor s E B →
          LocalParticleBound U A R P s.f ∧ GlobalFieldBound U L s.E s.B) := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
