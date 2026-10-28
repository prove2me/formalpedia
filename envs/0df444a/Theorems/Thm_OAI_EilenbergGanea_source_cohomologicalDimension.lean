-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_source_cohomologicalDimension
-- name    : OAI.EilenbergGanea.source_cohomologicalDimension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T00:13:19.618789+00:00
-- url     : https://prove2.me/theorems/962933cb-baf2-47fc-9402-4824498c851c
-- title:
--   Theorem 1.1 (cohomological dimension): the Eilenberg–Ganea source group has integral cohomological dimension two (OpenAI)
-- statement:
--   The part $\mathrm{cd}_{\mathbb Z} G = 2$ of the paper's Theorem 1.1 ("There is a finitely generated residually finite group $G$ such that $\mathrm{cd}_{\mathbb Z} G = 2$, $\mathrm{gd}\, G = 3$", p. 1), as OpenAI formalized it. It is one of the five conjuncts of `OAI.EilenbergGanea.source_main`, published on its own as an intermediate statement of the split of OpenAI's proof.
--
--   **Notation** (published bundle `Def_EilenbergGanea`). `SourceGroup` is the kernel of the height homomorphism on the right-angled Artin group `ArtinGroup seedGraph` (every standard generator to $1 \in \mathbb Z$), for OpenAI's 103-cell flag triangulation `seedGraph`. `cohomologicalDimension G`, a value in `WithBot ℕ∞`, is the projective dimension (`CategoryTheory.projectiveDimension`) of the trivial module $\mathbb Z$ in the category of left modules over the integral group ring `MonoidAlgebra ℤ G`.
--
--   **The statement.** `cohomologicalDimension SourceGroup = 2`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Theorem 1.1, p. 1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/Dimension.lean (declaration OAI.EilenbergGanea.source_cohomologicalDimension)

import Mathlib
import Definitions.Def_EilenbergGanea

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea

theorem source_cohomologicalDimension : cohomologicalDimension SourceGroup = 2 := by
  sorry

end EilenbergGanea

end

end OAI
end
