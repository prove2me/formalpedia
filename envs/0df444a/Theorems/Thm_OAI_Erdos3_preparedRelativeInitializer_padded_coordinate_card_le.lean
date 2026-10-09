-- Prove2me | Theorems.Thm_OAI_Erdos3_preparedRelativeInitializer_padded_coordinate_card_le
-- name    : OAI.Erdos3.preparedRelativeInitializer_padded_coordinate_card_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:24:59.718102+00:00
-- url     : https://prove2.me/theorems/8530f53c-eadf-4c4b-8f21-f00102364ff1
-- title:
--   Padding a rank-preparation family keeps every layer within the coordinate cap
-- statement:
--   Let $m, s, D, n_X$ be natural numbers and let `prep : RankPreparationFamily (Fin nX) (Fin D) m` be a family of $m$ rank-preparation layers (a `RankPreparationLayer`, for each index $j$ in $\mathrm{Fin}\,m$, is a structure bundling finite types `Coord`, `Column`, `Row`, a labelling `Coord → Fin D`, two rational matrices and a vector polynomial). Assume $m \le s$ and that for every $j$ the number of coordinates of the layer `prep j` is at most `preparationCoordinateCap m D (m * D)`, where `preparationCoordinateCap s D T` $= D\,(T+1)^s + D + T + 1$. Then for every $j$ in $\mathrm{Fin}(\max(m,s))$, the number of coordinates of layer $j$ of `prep.pad (max m s)` is at most `preparationCoordinateCap s D (s * D)`; here `prep.pad q` is the family of $q$ layers whose layer $j$ is `prep j` when $j < m$ and the empty layer otherwise.
--
--   Lean: `OAI.Erdos3.preparedRelativeInitializer_padded_coordinate_card_le` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean#L23

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {m s D nX : ℕ}

theorem preparedRelativeInitializer_padded_coordinate_card_le
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D)) :
    ∀ j, Fintype.card (prep.pad (max m s) j).Coord ≤
      preparationCoordinateCap s D (s * D) := by
  sorry

end Erdos3
end
end OAI
