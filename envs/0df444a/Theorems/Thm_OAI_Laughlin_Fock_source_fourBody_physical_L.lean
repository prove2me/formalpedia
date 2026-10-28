-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_source_fourBody_physical_L
-- name    : OAI.Laughlin.Fock.source_fourBody_physical_L
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:33:39.327863+00:00
-- url     : https://prove2.me/theorems/13d77792-614d-4c67-b9d4-be82c5739fb4
-- title:
--   OAI.Laughlin.Fock.source_fourBody_physical_L: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.source_fourBody_physical_L` of [lean/OAI/Analysis/Laughlin/FourBody/PhysicalSlaterReadout.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/PhysicalSlaterReadout.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`, `open Spin`):
--
--   ```lean
--   theorem source_fourBody_physical_L (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
--       (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
--       (hT : a.val+b.val+c.val+d.val=D+1) :
--       limitFourCopyEnd Q r D (create a (create b (create c (create d (1 : Space Q))))) =
--         ((Real.sqrt (sourceCopyWeight D r /
--           ((a.val.factorial : ℝ)*b.val.factorial*c.val.factorial*d.val.factorial)) *
--           (Certificate.L D r (a.val,b.val,c.val,d.val) : ℝ) : ℝ) : ℂ) • (1 : Space Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Certificate.L`, `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space` and `OAI.Laughlin.Fock.create` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Spin.sourceCopyWeight` (definitions bundle `OAIQ047L001` of this split); `OAI.Laughlin.Fock.limitFourCopyEnd` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proofs of `OAI_Laughlin_Fock_limitFourColumn_physical_L` and `OAI.Laughlin.Fock.source_fourBody_limitpositive` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/PhysicalSlaterReadout.lean (declaration OAI.Laughlin.Fock.source_fourBody_physical_L)

import Mathlib
import Definitions.Def_OAIQ047L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem source_fourBody_physical_L (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    limitFourCopyEnd Q r D (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt (sourceCopyWeight D r /
        ((a.val.factorial : ℝ)*b.val.factorial*c.val.factorial*d.val.factorial)) *
        (Certificate.L D r (a.val,b.val,c.val,d.val) : ℝ) : ℝ) : ℂ) • (1 : Space Q) := by
  sorry

end Laughlin.Fock

end OAI
end
