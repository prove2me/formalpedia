-- Prove2me | Theorems.Thm_OAI_RVM_transported_spatial_lipschitz
-- name    : OAI.RVM.transported_spatial_lipschitz
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:29:08.084976+00:00
-- url     : https://prove2.me/theorems/227306e9-ffb6-44b1-a18a-8118f04a4ad6
-- title:
--   OAI.RVM.transported_spatial_lipschitz: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.transported_spatial_lipschitz` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma transported_spatial_lipschitz {d : Datum} {s : Solution} {E B : Field}
--       (hs : PicardRegular d s) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
--       (hV : TransportFor s E B) {T A L N : ℝ} (hA : 0≤A) (hL : 0≤L) (hN : 0≤N)
--       (ha : ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖)
--       (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
--       (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
--       (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
--       {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
--       |s.f (t,z)-s.f (t,z')|≤(A*Real.exp ((1+2*N+L)*T))*‖z-z'‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PicardRegular` and `OAI.RVM.TransportFor` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.Field`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.exists_picard_field_limit` and `OAI.RVM.family_picard_field_limit` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardContraction.lean (declaration OAI.RVM.transported_spatial_lipschitz)

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

lemma transported_spatial_lipschitz {d : Datum} {s : Solution} {E B : Field}
    (hs : PicardRegular d s) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hV : TransportFor s E B) {T A L N : ℝ} (hA : 0≤A) (hL : 0≤L) (hN : 0≤N)
    (ha : ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
    |s.f (t,z)-s.f (t,z')|≤(A*Real.exp ((1+2*N+L)*T))*‖z-z'‖ := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
