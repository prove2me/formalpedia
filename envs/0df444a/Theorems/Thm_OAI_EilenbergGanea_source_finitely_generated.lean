-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_source_finitely_generated
-- name    : OAI.EilenbergGanea.source_finitely_generated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T00:12:54.574146+00:00
-- url     : https://prove2.me/theorems/d152503a-af5a-49f8-a1d9-4ebbc7af8efe
-- title:
--   Theorem 1.1 (finite generation): the Eilenberg–Ganea source group is finitely generated (OpenAI)
-- statement:
--   The finite-generation part of the paper's Theorem 1.1 ("There is a finitely generated residually finite group $G$ such that $\mathrm{cd}_{\mathbb Z} G = 2$, $\mathrm{gd}\, G = 3$", p. 1), as OpenAI formalized it. It is one of the five conjuncts of `OAI.EilenbergGanea.source_main`, published on its own as an intermediate statement of the split of OpenAI's proof.
--
--   **Notation** (published bundle `Def_EilenbergGanea`). `SourceGroup` is the kernel of the height homomorphism `height seedGraph`, which sends every standard generator of the right-angled Artin group `ArtinGroup seedGraph` to $1 \in \mathbb Z$; `seedGraph` is the comparability graph of the 103 cells (7 vertices, 51 edges, 45 sectors) of OpenAI's flag triangulation of the presentation complex of $\langle x, y \mid x^2 = y^5,\ x^2 = (xy^{-1})^3 \rangle$.
--
--   **The statement.** `Group.FG SourceGroup`: the height kernel is finitely generated.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Theorem 1.1, p. 1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/Model.lean (declaration OAI.EilenbergGanea.source_finitely_generated)

import Mathlib
import Definitions.Def_EilenbergGanea

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea
theorem source_finitely_generated : Group.FG SourceGroup := by
  sorry

end EilenbergGanea

end

end OAI
end
