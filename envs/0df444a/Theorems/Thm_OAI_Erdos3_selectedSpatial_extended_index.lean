-- Prove2me | Theorems.Thm_OAI_Erdos3_selectedSpatial_extended_index
-- name    : OAI.Erdos3.selectedSpatial_extended_index
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:07:08.533856+00:00
-- url     : https://prove2.me/theorems/75ea6b8e-1ea4-4c98-bb44-95ce3ce3e88b
-- title:
--   Index of the selected-pivot full image is at most B^(|I|+1)
-- statement:
--   Let $I,J,N$ be finite types, $\mathrm{root} : J\to\mathbb{Z}$, $D$ an $I\times J$ integer matrix, $s : I\hookrightarrow J$ an embedding, $C$ a $(\mathrm{Unit}\oplus I)\times N$ integer matrix, and $B$ a natural number. Assume `HasBoundedScalarPeriod (range D) B`: there is a natural number $a$ with $0<a\le B$ such that $a\,\mathbb{Z}^I$ is contained in the $\mathbb{Z}$-span $D\mathbb{Z}^J$ of the columns of $D$. Let $\Lambda$ be `pivotFullImage P F` (the sum of the $\mathbb{Z}$-column spans of $P$ and $F$, a $\mathbb{Z}$-submodule of $\mathbb{Z}^{\mathrm{Unit}\oplus I}$) for the pivot matrix $P=$ `selectedSpatialPivot root D s` (the `rootDifferenceMatrix` of $\mathrm{root}\circ s$ and the columns of $D$ selected by $s$) and the matrix $F$ obtained by placing `selectedSpatialFreeColumns root D s` (the columns of `rootDifferenceMatrix root D` at the elements of $J$ outside the range of $s$) side by side with $C$. Then the index of $\Lambda$ as a subgroup of $\mathbb{Z}^{\mathrm{Unit}\oplus I}$ is at most $B^{|I|+1}$.
--
--   Lean: `OAI.Erdos3.selectedSpatial_extended_index` in `lean/OAI/Combinatorics/Progressions/Geometry/ScalarSpatialScaleBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ScalarSpatialScaleBounds.lean#L39

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

namespace Erdos3

theorem selectedSpatial_extended_index {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {B : ℕ} (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    (pivotFullImage (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)).toAddSubgroup.index ≤
        B^(Fintype.card I + 1) := by
  sorry

end Erdos3
end OAI
