-- Prove2me | Theorems.Thm_OAI_RVM_mixed_magnetic_physical_representation
-- name    : OAI.RVM.mixed_magnetic_physical_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:27:12.904218+00:00
-- url     : https://prove2.me/theorems/13d1037a-ce1b-4fb9-a5f1-f8027f4950dd
-- title:
--   OAI.RVM.mixed_magnetic_physical_representation: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.mixed_magnetic_physical_representation` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/ElectricConeBoundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ElectricConeBoundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma mixed_magnetic_physical_representation {s : Solution} {E' B' : Field}
--       (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
--       (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
--       (hc : CompactOnFiniteHorizons s) (hV : TransportFor s s.E s.B)
--       (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
--       (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
--       (hM : MaxwellFor {s with E:=E',B:=B'}) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
--       B' (t,x) i = magneticConeBoundary {s with E:=E',B:=B'} t x i 0 +
--         (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z) i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.MaxwellFor`, `OAI.RVM.TransportFor`, `OAI.RVM.magneticConeBoundary` and `OAI.RVM.retardedMagneticDensity` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.CompactOnFiniteHorizons`, `OAI.RVM.Field`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.current`, `OAI.RVM.fieldHalfSpace` and `OAI.RVM.particleHalfSpace` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.exists_local_spatially_smooth_bounded_classical`, `OAI.RVM.exists_picard_field_limit`, `OAI.RVM.family_global_picard_invariance`, `OAI.RVM.family_local_spatially_smooth_bounded_classical`, `OAI.RVM.family_picard_field_limit` and `OAI.RVM.uniform_picard_sequence_jets` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ElectricConeBoundary.lean (declaration OAI.RVM.mixed_magnetic_physical_representation)

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

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma mixed_magnetic_physical_representation {s : Solution} {E' B' : Field}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s s.E s.B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor {s with E:=E',B:=B'}) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    B' (t,x) i = magneticConeBoundary {s with E:=E',B:=B'} t x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z) i) := by
  sorry

end RVM

end

end OAI
end
