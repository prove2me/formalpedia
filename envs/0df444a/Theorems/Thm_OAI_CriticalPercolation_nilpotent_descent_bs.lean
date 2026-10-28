-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_nilpotent_descent_bs
-- name    : OAI.CriticalPercolation.nilpotent_descent_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:33:14.683043+00:00
-- url     : https://prove2.me/theorems/997d9abe-7dd6-4260-be0b-ce8936215c0a
-- title:
--   OAI.CriticalPercolation.nilpotent_descent_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.nilpotent_descent` of [lean/OAI/Probability/CriticalPercolation/Nilpotent/NilpotentDescent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Nilpotent/NilpotentDescent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation`, with `open Set Function`, `open scoped Classical`):
--
--   ```lean
--   theorem nilpotent_descent_bs (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G] :
--       AlgebraicDescent G
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.AlgebraicDescent` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Nilpotent/NilpotentDescent.lean (declaration OAI.CriticalPercolation.nilpotent_descent)

import Mathlib
import Definitions.Def_OAIQ078B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_descent_bs (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G] :
    AlgebraicDescent G := by
  sorry

end CriticalPercolation
end
end
end

end OAI
end
