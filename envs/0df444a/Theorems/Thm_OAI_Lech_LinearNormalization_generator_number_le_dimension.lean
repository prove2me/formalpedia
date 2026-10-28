-- Prove2me | Theorems.Thm_OAI_Lech_LinearNormalization_generator_number_le_dimension
-- name    : OAI.Lech.LinearNormalization.generator_number_le_dimension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:24:14.592308+00:00
-- url     : https://prove2.me/theorems/c9001b14-3a08-4244-8f70-c84a572d0c65
-- title:
--   OAI.Lech.LinearNormalization.generator_number_le_dimension: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.LinearNormalization`, with `open DirectSum MvPolynomial`):
--
--   ```lean
--   lemma generator_number_le_dimension {s : ℕ}
--       (z : Fin s → IdealGraded.Ring (IsLocalRing.maximalIdeal R))
--       (hz : ∀ i,z i ∈ IdealGraded.grade (IsLocalRing.maximalIdeal R) 1)
--       (hi : Function.Injective (aeval (R:=R ⧸ IsLocalRing.maximalIdeal R) z)) :
--       s ≤ dimension R
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IdealGraded.Ring`, `OAI.Lech.IdealGraded.gradedAlgebra` and `OAI.Lech.IdealGraded.shifted` (definitions bundle `OAIQ032L003` of this split); `OAI.Lech.IdealGraded.grade` (definitions bundle `OAIQ032L012` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.MinimalReduction.exists_reduction` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L012

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DirectSum MvPolynomial
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma generator_number_le_dimension {s : ℕ}
    (z : Fin s → IdealGraded.Ring (IsLocalRing.maximalIdeal R))
    (hz : ∀ i,z i ∈ IdealGraded.grade (IsLocalRing.maximalIdeal R) 1)
    (hi : Function.Injective (aeval (R:=R ⧸ IsLocalRing.maximalIdeal R) z)) :
    s ≤ dimension R := by
  sorry
end Lech.LinearNormalization

end

end OAI
end
