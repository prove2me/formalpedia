-- Prove2me | Theorems.Thm_OAI_Erdos3_RankPreparationFamily_PreparedHeights_euclideanJetLayers_compact
-- name    : OAI.Erdos3.RankPreparationFamily.PreparedHeights.euclideanJetLayers_compact
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T08:12:52.029751+00:00
-- url     : https://prove2.me/theorems/c038fab4-7f60-472a-8ee6-29fad137d4e6
-- title:
--   The Euclidean jet layers of a prepared rank-preparation family form a compact space
-- statement:
--   Let $X$, $J$ be types, $m$ a natural number and `L : RankPreparationFamily X J m` a family of $m$ rank-preparation layers (each a structure bundling a finite coordinate type, two rational matrices, a vector polynomial and more; `(L j).space` is the real subspace of $\mathbb R^{\mathrm{Coord}}$ cut out by its matrices). Let $p$ be a real number and $R$ a natural number, and assume `L.PreparedHeights p R` (each layer $i$ is `Valid` with degree $i+1$, an explicit height bound `preparationHeight p (m - 1 - i)` and row height bound $R$), $0 \le p$ and $1 \le R$. Then for every family of types $O : \mathrm{Fin}\,m \to \mathrm{Type}$, the space `EuclideanJetLayers (fun j => (L j).space) O` is compact; this is the product over $j \in \mathrm{Fin}\,m$ and $o \in O_j$ of the quotient of the Euclidean copy of `(L j).space` by its intersection with the standard integer lattice.
--
--   Lean: `OAI.Erdos3.RankPreparationFamily.PreparedHeights.euclideanJetLayers_compact` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativePositivePassage.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B129` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativePositivePassage.lean#L16

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B129

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.euclideanJetLayers_compact
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (O : Fin m → Type*) :
    CompactSpace (EuclideanJetLayers (fun j => (L j).space) O) := by
  sorry

end Erdos3.RankPreparationFamily
end
end OAI
