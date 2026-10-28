-- Prove2me | Theorems.Thm_OAI_Lech_TensorGenerator_scalar_cokernel_le
-- name    : OAI.Lech.TensorGenerator.scalar_cokernel_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:17:05.004912+00:00
-- url     : https://prove2.me/theorems/19ca3b5b-4787-4042-bedd-75f857a01e1b
-- title:
--   OAI.Lech.TensorGenerator.scalar_cokernel_le: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.TensorGenerator`, with `open scoped TensorProduct ENNReal`):
--
--   ```lean
--   lemma scalar_cokernel_le (hf : Function.Surjective f) (I : Ideal D)
--       (hI : I ≤ Module.annihilator D M) (g : R) :
--       T.length ((B ⊗[D] M) ⧸ (LinearMap.lsmul R (B ⊗[D] M) g).range) ≤
--         (b : ℝ≥0∞) * T.length (B ⧸ (I.map (algebraMap D B) ⊔
--           Ideal.span {algebraMap R B g}))
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
namespace Lech.TensorGenerator
variable {D M : Type*} [CommRing D] [AddCommGroup M] [Module D M]

variable {b : ℕ} (f : (Fin b → D) →ₗ[D] M)
  (B : Type*) [CommRing B] [Algebra D B]

variable {R : Type*} [CommRing R] (T : Lech.NormalizedLength.Tower R)
  [Algebra R B]

lemma scalar_cokernel_le (hf : Function.Surjective f) (I : Ideal D)
    (hI : I ≤ Module.annihilator D M) (g : R) :
    T.length ((B ⊗[D] M) ⧸ (LinearMap.lsmul R (B ⊗[D] M) g).range) ≤
      (b : ℝ≥0∞) * T.length (B ⧸ (I.map (algebraMap D B) ⊔
        Ideal.span {algebraMap R B g})) := by
  sorry
end Lech.TensorGenerator

end

end OAI
end
