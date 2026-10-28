-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_finiteAffineNoiseLaw_close
-- name    : OAI.SimpleAmenable.finiteAffineNoiseLaw_close
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:20:49.995041+00:00
-- url     : https://prove2.me/theorems/e6b1a5f3-b148-4f07-86ef-eb6835855d87
-- title:
--   OAI.SimpleAmenable.finiteAffineNoiseLaw_close: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.finiteAffineNoiseLaw_close` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/FiniteLawDistance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/FiniteLawDistance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical Matrix MeasureTheory`):
--
--   ```lean
--   theorem finiteAffineNoiseLaw_close {ι : Type*} [Fintype ι]
--       (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ) :
--       ObservableClose (finiteAffineNoiseLaw (1+B) a) (finiteAffineNoiseLaw (1+C) (a+h))
--         (smoothNoiseTransportError B C h)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.ObservableClose`, `OAI.SimpleAmenable.finiteAffineNoiseLaw` and `OAI.SimpleAmenable.smoothNoiseTransportError` (definitions bundle `OAIQ65Sa002` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.finiteSignalFields_transport` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/FiniteLawDistance.lean (declaration OAI.SimpleAmenable.finiteAffineNoiseLaw_close)

import Mathlib
import Definitions.Def_OAIQ65Sa002

section

attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteLawDistance
open Classical Matrix MeasureTheory

theorem finiteAffineNoiseLaw_close {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ) :
    ObservableClose (finiteAffineNoiseLaw (1+B) a) (finiteAffineNoiseLaw (1+C) (a+h))
      (smoothNoiseTransportError B C h) := by
  sorry

end FiniteLawDistance

end SimpleAmenable
end
end

end OAI
end
