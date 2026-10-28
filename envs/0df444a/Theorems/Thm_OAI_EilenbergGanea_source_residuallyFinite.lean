-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_source_residuallyFinite
-- name    : OAI.EilenbergGanea.source_residuallyFinite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T00:13:38.171445+00:00
-- url     : https://prove2.me/theorems/a3f3d487-e14a-479c-9fcc-09477bdc1122
-- title:
--   Theorem 1.1 (residual finiteness): the Eilenberg–Ganea source group is residually finite (OpenAI)
-- statement:
--   The residual-finiteness part of the paper's Theorem 1.1 ("There is a finitely generated residually finite group $G$ such that $\mathrm{cd}_{\mathbb Z} G = 2$, $\mathrm{gd}\, G = 3$", p. 1), as OpenAI formalized it; the paper proves it in Lemma 4.2 ("In particular, $P$ and $G$ are residually finite", p. 14). It is one of the five conjuncts of `OAI.EilenbergGanea.source_main`, published on its own as an intermediate statement of the split of OpenAI's proof.
--
--   **Notation** (published bundle `Def_EilenbergGanea`). `SourceGroup` is the kernel of the height homomorphism `height seedGraph` on the right-angled Artin group `ArtinGroup seedGraph`, which sends every standard generator to $1 \in \mathbb Z$; `seedGraph` is the comparability graph of the 103 cells of OpenAI's flag triangulation of the presentation complex of $\langle x, y \mid x^2 = y^5,\ x^2 = (xy^{-1})^3 \rangle$.
--
--   **The statement.** `Group.ResiduallyFinite SourceGroup`. It follows from `OAI.EilenbergGanea.artin_residuallyFinite` (the first sentence of Lemma 4.2, for every finite graph), since a subgroup of a residually finite group is residually finite.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Theorem 1.1, p. 1, and Lemma 4.2, p. 14; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/Model.lean (declaration OAI.EilenbergGanea.source_residuallyFinite)

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
theorem source_residuallyFinite : Group.ResiduallyFinite SourceGroup := by
  sorry

end EilenbergGanea

end

end OAI
end
