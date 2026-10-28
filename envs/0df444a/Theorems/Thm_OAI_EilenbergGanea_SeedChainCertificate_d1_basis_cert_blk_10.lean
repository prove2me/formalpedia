-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_10
-- name    : OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_10
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:10:46.10955+00:00
-- url     : https://prove2.me/theorems/ccd9a9d4-cee6-463e-8c38-056f172b50f6
-- title:
--   Seed chain certificate, block 10: rows 100–102 of the first boundary matrix of the 103-vertex flag complex are correct (OpenAI Eilenberg–Ganea)
-- statement:
--   One block of OpenAI's finite check `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert`, part of the certificate that the flag complex $L$ of the paper's Section 4 is integrally acyclic. This split groups OpenAI's per-vertex lemmas into blocks so that each can be verified separately; the statement is an intermediate statement of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`.
--
--   **Notation** (definitions bundles of this split, namespace `OAI.EilenbergGanea.SeedChainCertificate`). OpenAI encodes the flag complex (the order complex of the 103 cells of the seed triangulation `seedGraph`) by tables: 103 vertices, 372 edges `edge e` (a pair of vertices) and 270 triangles. `d1Row v` is the row of the vertex $v$ in the first boundary matrix, a list of (edge, coefficient) pairs, and `rowEval r c` is $\sum_{(k, a) \in r} a \cdot c(k)$.
--
--   **The statement.** For every vertex $i$ with $100 \le i < 103$ and every edge $e$, evaluating the row `d1Row i` on the indicator of $e$ gives $[i = \text{end of } e] - [i = \text{start of } e]$.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Section 4; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean (the per-index lemmas d1_basis_cert_100 to d1_basis_cert_102; the block statement is this split's grouping)

import Mathlib
import Definitions.Def_OAIEGC000

section

attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem d1_basis_cert_blk_10 (i : Fin 103) (hb : 100 ≤ i.val ∧ i.val < 103) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  sorry

end EilenbergGanea.SeedChainCertificate

end

end OAI
end
