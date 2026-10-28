-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert
-- name    : OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:00:00.961921+00:00
-- url     : https://prove2.me/theorems/e468f53c-1651-4c64-97d4-3688a4d9dfd2
-- title:
--   Seed chain certificate: the second boundary matrix of the 103-vertex flag complex is correct (OpenAI Eilenberg–Ganea)
-- statement:
--   A finite computation in OpenAI's certificate that the flag complex $L$ of the paper's Section 4 is integrally acyclic. It is an intermediate statement of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, published on its own because the chain contraction (a definition) rests on it.
--
--   **Notation** (definitions bundles of this split, namespace `OAI.EilenbergGanea.SeedChainCertificate`). OpenAI encodes the flag complex (the order complex of the 103 cells of the seed triangulation `seedGraph`) by tables: 103 vertices, 372 edges and 270 triangles `triangleEdges t`, each a triple $(e_1, e_2, e_3)$ of edges. `d2Row e` is the row of the edge $e$ in the second boundary matrix, a list of (triangle, coefficient) pairs, and `rowEval r c` is $\sum_{(k, a) \in r} a \cdot c(k)$.
--
--   **The statement.** For every edge $e$ and triangle $t$ with edges $(e_1, e_2, e_3)$, evaluating the row `d2Row e` on the indicator of $t$ gives $[e = e_1] - [e = e_2] + [e = e_3]$: the matrix columns are the boundaries $\partial t = e_1 - e_2 + e_3$. OpenAI proves it from 372 per-edge `decide +kernel` checks; this split groups them into blocks of 30 indices.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Section 4; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean (declaration OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert)

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

theorem d2_basis_cert (e : Fin 372) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  sorry

end EilenbergGanea.SeedChainCertificate

end

end OAI
end
