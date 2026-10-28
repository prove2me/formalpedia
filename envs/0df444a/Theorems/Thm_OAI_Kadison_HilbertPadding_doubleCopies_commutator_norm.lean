-- Prove2me | Theorems.Thm_OAI_Kadison_HilbertPadding_doubleCopies_commutator_norm
-- name    : OAI.Kadison.HilbertPadding.doubleCopies_commutator_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:42:58.696373+00:00
-- url     : https://prove2.me/theorems/c401c630-fcb1-4b79-9757-0bd51db71e9f
-- title:
--   OAI.Kadison.HilbertPadding.doubleCopies_commutator_norm: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.HilbertPadding`, with `open scoped BigOperators InnerProductSpace`, `open ContinuousLinearMap`, `open OperatorAmplification`):
--
--   ```lean
--   theorem doubleCopies_commutator_norm
--       (Y : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (a : H →L[ℂ] H) :
--       ‖extend (doubleCopies ι) Y*diagonal (H:=H) ((Fin 2)×ι) a-
--         diagonal (H:=H) ((Fin 2)×ι) a*extend (doubleCopies ι) Y‖=
--           ‖Y*diagonal (H:=H) ι a-diagonal (H:=H) ι a*Y‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.HilbertPadding.extend` (definitions bundle `OAIQ039C012` of this split); `OAI.Kadison.HilbertPadding.doubleCopies` (definitions bundle `OAIQ039C027` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.square_contraction_after_average` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C027

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

theorem doubleCopies_commutator_norm
    (Y : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (a : H →L[ℂ] H) :
    ‖extend (doubleCopies ι) Y*diagonal (H:=H) ((Fin 2)×ι) a-
      diagonal (H:=H) ((Fin 2)×ι) a*extend (doubleCopies ι) Y‖=
        ‖Y*diagonal (H:=H) ι a-diagonal (H:=H) ι a*Y‖ := by
  sorry

end Kadison.HilbertPadding

end

end
end

end OAI
end
