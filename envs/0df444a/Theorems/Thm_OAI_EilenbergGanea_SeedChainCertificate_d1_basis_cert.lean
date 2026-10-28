-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert
-- name    : OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:07:12.331391+00:00
-- url     : https://prove2.me/theorems/211722cd-b998-480b-a12c-7d0c4a57db13
-- title:
--   Seed chain certificate: the first boundary matrix of the 103-vertex flag complex is correct (OpenAI Eilenberg–Ganea)
-- statement:
--   A finite computation in OpenAI's certificate that the flag complex $L$ of the paper's Section 4 is integrally acyclic. It is an intermediate statement of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, published on its own because the chain contraction (a definition) rests on it.
--
--   **Notation** (definitions bundles of this split, namespace `OAI.EilenbergGanea.SeedChainCertificate`). OpenAI encodes the flag complex (the order complex of the 103 cells of the seed triangulation `seedGraph`) by tables: 103 vertices, 372 edges `edge e` (a pair of vertices) and 270 triangles `triangleEdges t` (a triple of edges). `d1Row v` is the row of the vertex $v$ in the first boundary matrix, a list of (edge, coefficient) pairs, and `rowEval r c` is $\sum_{(k, a) \in r} a \cdot c(k)$.
--
--   **The statement.** For every vertex $i$ and edge $e$, evaluating the row `d1Row i` on the indicator of $e$ gives $[i = \text{end of } e] - [i = \text{start of } e]$: the matrix rows are the boundary $\partial e = (\text{end}) - (\text{start})$ of every edge. OpenAI proves it from 103 per-vertex `decide +kernel` checks; this split groups them into blocks of 10 indices.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Section 4; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean (declaration OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert)

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

theorem d1_basis_cert (i : Fin 103) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  sorry

end EilenbergGanea.SeedChainCertificate

end

end OAI
end
