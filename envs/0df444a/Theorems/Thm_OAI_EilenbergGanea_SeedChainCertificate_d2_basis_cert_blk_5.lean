-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_5
-- name    : OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_5
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:01:37.274961+00:00
-- url     : https://prove2.me/theorems/43791c20-064b-47b8-adc8-a4eea7f91146
-- title:
--   OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_5: intermediate lemma from OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_5` of [lean/OAI/Topology/EilenbergGanea/SeedContraction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EilenbergGanea.SeedChainCertificate`, with `open Classical Set`):
--
--   ```lean
--   theorem d2_basis_cert_blk_5 (e : Fin 372) (hb : 150 ≤ e.val ∧ e.val < 180) (t : Fin 270) :
--       rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
--         (if e = (triangleEdges t).1 then 1 else 0) -
--         (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EilenbergGanea.SeedChainCertificate.rowEval` (definitions bundle `OAIEG001` of this split); `OAI.EilenbergGanea.SeedChainCertificate.d2Row` and `OAI.EilenbergGanea.SeedChainCertificate.triangleEdges` (definitions bundle `OAIEG002` of this split).
--
--   **Used by.** The proof of `OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert` of this split imports it.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean (declaration OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_5)

import Mathlib
import Definitions.Def_OAIEG001
import Definitions.Def_OAIEG002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem d2_basis_cert_blk_5 (e : Fin 372) (hb : 150 ≤ e.val ∧ e.val < 180) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  sorry

end EilenbergGanea.SeedChainCertificate

end

end OAI
end
