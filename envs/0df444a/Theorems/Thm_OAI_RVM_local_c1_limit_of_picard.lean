-- Prove2me | Theorems.Thm_OAI_RVM_local_c1_limit_of_picard
-- name    : OAI.RVM.local_c1_limit_of_picard
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:26:43.424993+00:00
-- url     : https://prove2.me/theorems/88fc5ee8-318d-46f7-a4ff-1e9e213732d5
-- title:
--   OAI.RVM.local_c1_limit_of_picard: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.local_c1_limit_of_picard` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/SlabEquations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/SlabEquations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma local_c1_limit_of_picard {d : Datum} {S : ℕ → Solution} {s : Solution}
--       {T A R P H Hf M L : ℝ} (hT : 0<T) (hH : 0≤H) (hHf : 0≤Hf) (hM : 0≤M) (hL : 0≤L)
--       (hr : ∀ n, PicardRegular d (S (n+1)))
--       (htransport : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
--       (hc : ∀ n, SpatialFieldCurvature T H (S n).E (S n).B)
--       (hcf : ∀ n, PhaseParticleCurvature T Hf (S (n+1)).f)
--       (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
--       (hlip : ∀ n, PhaseParticleLip T M (S (n+1)).f)
--       (hlb : GlobalFieldBound T L s.E s.B)
--       (hbf : LocalParticleBound T A R P s.f)
--       (hfc : ContinuousOn s.f (particleSlab T))
--       (hfl : TendstoUniformlyOn (fun n => (S (n+1)).f) s.f atTop (particleSlab T))
--       (hEl : TendstoUniformlyOn (fun n => (S n).E) s.E atTop (fieldSlab T))
--       (hBl : TendstoUniformlyOn (fun n => (S n).B) s.B atTop (fieldSlab T)) :
--       ContDiffOn ℝ 1 s.f (particleSlab T) ∧ ContDiffOn ℝ 1 s.E (fieldSlab T) ∧
--         ContDiffOn ℝ 1 s.B (fieldSlab T) ∧ SlabEquations s T
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.GlobalFieldBound`, `OAI.RVM.LocalParticleBound`, `OAI.RVM.PhaseParticleCurvature`, `OAI.RVM.PhaseParticleLip`, `OAI.RVM.PicardRegular`, `OAI.RVM.SlabEquations`, `OAI.RVM.SpatialFieldCurvature` and `OAI.RVM.TransportFor` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.fieldSlab` and `OAI.RVM.particleSlab` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.exists_local_spatially_smooth_bounded_classical` and `OAI.RVM.family_local_spatially_smooth_bounded_classical` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/SlabEquations.lean (declaration OAI.RVM.local_c1_limit_of_picard)

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

lemma local_c1_limit_of_picard {d : Datum} {S : ℕ → Solution} {s : Solution}
    {T A R P H Hf M L : ℝ} (hT : 0<T) (hH : 0≤H) (hHf : 0≤Hf) (hM : 0≤M) (hL : 0≤L)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (htransport : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hc : ∀ n, SpatialFieldCurvature T H (S n).E (S n).B)
    (hcf : ∀ n, PhaseParticleCurvature T Hf (S (n+1)).f)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hlip : ∀ n, PhaseParticleLip T M (S (n+1)).f)
    (hlb : GlobalFieldBound T L s.E s.B)
    (hbf : LocalParticleBound T A R P s.f)
    (hfc : ContinuousOn s.f (particleSlab T))
    (hfl : TendstoUniformlyOn (fun n => (S (n+1)).f) s.f atTop (particleSlab T))
    (hEl : TendstoUniformlyOn (fun n => (S n).E) s.E atTop (fieldSlab T))
    (hBl : TendstoUniformlyOn (fun n => (S n).B) s.B atTop (fieldSlab T)) :
    ContDiffOn ℝ 1 s.f (particleSlab T) ∧ ContDiffOn ℝ 1 s.E (fieldSlab T) ∧
      ContDiffOn ℝ 1 s.B (fieldSlab T) ∧ SlabEquations s T := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
