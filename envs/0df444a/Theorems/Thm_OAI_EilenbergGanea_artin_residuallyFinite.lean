-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_artin_residuallyFinite
-- name    : OAI.EilenbergGanea.artin_residuallyFinite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T00:11:45.324449+00:00
-- url     : https://prove2.me/theorems/6074d086-e54a-47df-a98f-f837ecb5d2d3
-- title:
--   Lemma 4.2: right-angled Artin groups of finite graphs are residually finite (OpenAI)
-- statement:
--   The first sentence of the paper's Lemma 4.2 ("The group associated to any finite commutation graph is residually finite", p. 14), as OpenAI formalized it. The paper notes that the result is classical for graph products of residually finite groups and gives a direct induction on the number of vertices, via retractions and a semidirect splitting. It is an intermediate statement of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`.
--
--   **Notation** (published bundle `Def_EilenbergGanea`). For a simple graph $L$ on a type $V$, `ArtinGroup L` is the right-angled Artin group of $L$: the presented group on the vertices with the relation $a b a^{-1} b^{-1} = 1$ for each pair of adjacent vertices $a, b$.
--
--   **The statement.** For every finite type $V$ (in any universe) and every simple graph $L$ on $V$, `Group.ResiduallyFinite (ArtinGroup L)`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Lemma 4.2, p. 14; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/RightAngledArtin/ResidualFiniteness.lean (declaration OAI.EilenbergGanea.artin_residuallyFinite)

import Mathlib
import Definitions.Def_EilenbergGanea

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
universe u

theorem artin_residuallyFinite (V : Type u) [Finite V] (L : SimpleGraph V) :
    Group.ResiduallyFinite (ArtinGroup L) := by
  sorry

end EilenbergGanea

end

end OAI
end
