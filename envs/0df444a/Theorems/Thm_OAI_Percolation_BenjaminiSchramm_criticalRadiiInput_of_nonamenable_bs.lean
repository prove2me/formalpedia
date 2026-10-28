-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_criticalRadiiInput_of_nonamenable_bs
-- name    : OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:36:44.199959+00:00
-- url     : https://prove2.me/theorems/8d6b1322-b0a7-45c9-bf40-5aecb02b9f3f
-- title:
--   OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable` of [lean/OAI/Probability/BenjaminiSchramm/RadiusTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/RadiusTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem criticalRadiiInput_of_nonamenable_bs [Infinite V]
--       (G : BondGraph V E) (hh : 0 < hV G) : HutchcroftCriticalRadiiInput G
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.BenjaminiSchramm.HutchcroftCriticalRadiiInput` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph` and `OAI.Percolation.hV` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.full_application_gap_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/RadiusTransfer.lean (declaration OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem criticalRadiiInput_of_nonamenable_bs [Infinite V]
    (G : BondGraph V E) (hh : 0 < hV G) : HutchcroftCriticalRadiiInput G := by
  sorry

end Percolation.BenjaminiSchramm

end OAI
end
