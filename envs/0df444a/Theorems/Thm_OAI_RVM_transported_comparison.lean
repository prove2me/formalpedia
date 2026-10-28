-- Prove2me | Theorems.Thm_OAI_RVM_transported_comparison
-- name    : OAI.RVM.transported_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:29:14.971086+00:00
-- url     : https://prove2.me/theorems/c313acd6-b41b-46af-9638-470971a934e9
-- title:
--   OAI.RVM.transported_comparison: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.transported_comparison` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma transported_comparison {d : Datum} {s s' : Solution} {E B E' B' : Field}
--       (hf : ContDiff ℝ ∞ s.f) (hg : ContDiff ℝ ∞ s'.f)
--       (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
--       (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
--       (hV : TransportFor s E B) (hV' : TransportFor s' E' B')
--       (h₀ : ∀ z, s.f (0,z)=d.f₀ z) (h₀' : ∀ z, s'.f (0,z)=d.f₀ z)
--       {T A L N D : ℝ} (hA : 0≤A) (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
--       (ha : ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖)
--       (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
--       (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
--       (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
--       (hEd : ∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
--       (hBd : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)-B' (t,x)‖≤D)
--       {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
--       |s.f (t,z)-s'.f (t,z')|≤A*(‖z-z'‖+2*D*t)*Real.exp ((1+2*N+L)*t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.TransportFor` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.Field`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.exists_local_spatially_smooth_bounded_classical`, `OAI.RVM.exists_picard_field_limit`, `OAI.RVM.family_local_spatially_smooth_bounded_classical`, `OAI.RVM.family_picard_field_limit` and `OAI.RVM.transported_spatial_lipschitz` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean (declaration OAI.RVM.transported_comparison)

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

lemma transported_comparison {d : Datum} {s s' : Solution} {E B E' B' : Field}
    (hf : ContDiff ℝ ∞ s.f) (hg : ContDiff ℝ ∞ s'.f)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hV : TransportFor s E B) (hV' : TransportFor s' E' B')
    (h₀ : ∀ z, s.f (0,z)=d.f₀ z) (h₀' : ∀ z, s'.f (0,z)=d.f₀ z)
    {T A L N D : ℝ} (hA : 0≤A) (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
    (ha : ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEd : ∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
    (hBd : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)-B' (t,x)‖≤D)
    {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
    |s.f (t,z)-s'.f (t,z')|≤A*(‖z-z'‖+2*D*t)*Real.exp ((1+2*N+L)*t) := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
