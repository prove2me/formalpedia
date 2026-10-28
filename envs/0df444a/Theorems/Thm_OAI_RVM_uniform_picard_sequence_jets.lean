-- Prove2me | Theorems.Thm_OAI_RVM_uniform_picard_sequence_jets
-- name    : OAI.RVM.uniform_picard_sequence_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:29:35.487626+00:00
-- url     : https://prove2.me/theorems/d55e2744-f49e-4786-94f9-1c13691cf6c5
-- title:
--   OAI.RVM.uniform_picard_sequence_jets: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.uniform_picard_sequence_jets` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardCurvature.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardCurvature.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem uniform_picard_sequence_jets {d : Datum} (hd : Admissible d)
--       {S : ℕ → Solution} {T A R P L N M : ℝ} (_ : 0<T) (hT1 : T≤1)
--       (hN : 0≤N) (hM : 0≤M) (h0 : S 0=datumBoundarySolution d)
--       (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
--       (hc : ∀ n, FieldControl T L N (S n).E (S n).B)
--       (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
--         LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) :
--       ∀ k : ℕ, ∃ Q : ℝ, 1≤Q ∧
--         (∀ n, SpatialJetBound (k+1) T Q (S n).E (S n).B) ∧
--         ∀ n, ParticleJetBound (k+1) T Q (S (n+1)).f
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.FieldControl`, `OAI.RVM.LocalParticleBound`, `OAI.RVM.ParticleJetBound`, `OAI.RVM.PhaseParticleLip`, `OAI.RVM.PicardRegular`, `OAI.RVM.SpatialJetBound`, `OAI.RVM.TransportFor` and `OAI.RVM.datumBoundarySolution` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.exists_local_spatially_smooth_bounded_classical` and `OAI.RVM.family_local_spatially_smooth_bounded_classical` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardCurvature.lean (declaration OAI.RVM.uniform_picard_sequence_jets)

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

theorem uniform_picard_sequence_jets {d : Datum} (hd : Admissible d)
    {S : ℕ → Solution} {T A R P L N M : ℝ} (_ : 0<T) (hT1 : T≤1)
    (hN : 0≤N) (hM : 0≤M) (h0 : S 0=datumBoundarySolution d)
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hc : ∀ n, FieldControl T L N (S n).E (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
      LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) :
    ∀ k : ℕ, ∃ Q : ℝ, 1≤Q ∧
      (∀ n, SpatialJetBound (k+1) T Q (S n).E (S n).B) ∧
      ∀ n, ParticleJetBound (k+1) T Q (S (n+1)).f := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
