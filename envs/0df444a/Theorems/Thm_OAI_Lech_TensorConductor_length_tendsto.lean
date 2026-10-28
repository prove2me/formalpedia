-- Prove2me | Theorems.Thm_OAI_Lech_TensorConductor_length_tendsto
-- name    : OAI.Lech.TensorConductor.length_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:16:14.985413+00:00
-- url     : https://prove2.me/theorems/da6bb533-d1ba-4922-a351-5f2529e05a19
-- title:
--   OAI.Lech.TensorConductor.length_tendsto: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.TensorConductor`, with `open scoped TensorProduct ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem length_tendsto (T : NormalizedLength.Tower R)
--       (hm : Monotone B) (hex : ∀ c : C, ∃ n, c ∈ B n)
--       (g : ℕ → R) (hg : ∀ n c, g n • c ∈ B n)
--       (hfinite : ∀ n, T.length ((B n) ⊗[D] M) ≠ ⊤)
--       (herr : Tendsto (fun n => T.length (((B n) ⊗[D] M) ⧸
--         (LinearMap.lsmul R ((B n) ⊗[D] M) (g n)).range)) atTop (𝓝 0)) :
--       Tendsto (fun n => T.length ((B n) ⊗[D] M)) atTop
--         (𝓝 (T.length (C ⊗[D] M)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.NormalizedLength.Tower` and `OAI.Lech.NormalizedLength.Tower.length` (definitions bundle `OAIQ032L006` of this split).
--
--   **Used by.** The proof of `OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L006

section

attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.TensorConductor

section Stages
variable {D R C : Type*} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : ℕ → Subalgebra R C) [∀ n, Algebra D (B n)]
  [∀ n, IsScalarTower D (B n) C]
  (M : Type*) [AddCommGroup M] [Module D M]

open Filter
open scoped Topology

theorem length_tendsto (T : NormalizedLength.Tower R)
    (hm : Monotone B) (hex : ∀ c : C, ∃ n, c ∈ B n)
    (g : ℕ → R) (hg : ∀ n c, g n • c ∈ B n)
    (hfinite : ∀ n, T.length ((B n) ⊗[D] M) ≠ ⊤)
    (herr : Tendsto (fun n => T.length (((B n) ⊗[D] M) ⧸
      (LinearMap.lsmul R ((B n) ⊗[D] M) (g n)).range)) atTop (𝓝 0)) :
    Tendsto (fun n => T.length ((B n) ⊗[D] M)) atTop
      (𝓝 (T.length (C ⊗[D] M))) := by
  sorry
end Stages
end Lech.TensorConductor

end

end OAI
end
