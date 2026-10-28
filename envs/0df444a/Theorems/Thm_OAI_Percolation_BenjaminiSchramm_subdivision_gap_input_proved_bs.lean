-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_subdivision_gap_input_proved_bs
-- name    : OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:39:57.782783+00:00
-- url     : https://prove2.me/theorems/0d8c4098-66a0-43d2-a2c1-a37a919bb640
-- title:
--   OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved` of [lean/OAI/Probability/BenjaminiSchramm/UnconditionalInputs.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/UnconditionalInputs.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`):
--
--   ```lean
--   theorem subdivision_gap_input_proved_bs
--       (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
--       (hq : QuasiTransitive G) (hh : 0 < hV G) :
--       ¬ AutUnimodular (subdivision G) (subdivision_injective G)
--         (subdivision_connected G hc) (subdivision_locallyFinite G hl) →
--       pc (subdivision G) < ptwo (subdivision G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.SubdivisionEdge` and `OAI.Percolation.subdivision` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.AutUnimodular`, `OAI.Percolation.subdivision_connected`, `OAI.Percolation.subdivision_injective` and `OAI.Percolation.subdivision_locallyFinite` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.hV`, `OAI.Percolation.pc` and `OAI.Percolation.ptwo` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proofs of `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/UnconditionalInputs.lean (declaration OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm
universe u v
variable {V : Type u} {E : Type v} [Infinite V]

theorem subdivision_gap_input_proved_bs
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) :
    ¬ AutUnimodular (subdivision G) (subdivision_injective G)
      (subdivision_connected G hc) (subdivision_locallyFinite G hl) →
    pc (subdivision G) < ptwo (subdivision G) := by
  sorry

end Percolation.BenjaminiSchramm

end OAI
end
