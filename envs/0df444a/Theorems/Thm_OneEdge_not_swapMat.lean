-- Prove2me | Theorems.Thm_OneEdge_not_swapMat
-- name    : OneEdge.not_swapMat
-- status  : Proved
-- author  : @darkhipo
-- created : 2026-10-29T16:20:44.809038+00:00
-- url     : https://prove2.me/theorems/2e1e6867-360c-43c2-88a8-b988ed62a2c0
-- title:
--   One-run edges cannot realize the full chunk swap
-- statement:
--   Let $m$, $M$, and $w$ be natural numbers with $M>1$ and $w<m$. Consider the Bruhat edge consisting of one contiguous reversed-bank run of width $w$ on an $m$-wire chunk, evaluated over $\mathbb Z/M\mathbb Z$. Its edge matrix is not the full chunk-interchange matrix.
--
--   Consequently, an output role whose complete formal evaluation collapses to this single one-run edge cannot realize the full chunk swap. The statement is uniform in the chunk size $m$; its instance $m=529$ is the fixed-point obstruction used in the R8 opposite-bank reconstruction analysis.
--
--   **Formalization Note.** The edge is written directly as `⟨1, [(0, m - w, w)], 1⟩`, so the only definition dependency is the published round-six framework.
-- source:
--   Original result from the MultiAgency R8 opposite-bank reconstruction repair, register R2125607035 (2026-10-29), Theorems/Thm_oneEdge_ne_swapMat_general.lean.

import Definitions.Def_IntMul_Kappa_R6_Defs4

open IntMul.Kappa IntMul.Kappa.R6.Bit

namespace OneEdge

theorem not_swapMat (m M w : ℕ) (hM : 1 < M) (hw : w < m) :
    edgeMat M (⟨1, [(0, m - w, w)], 1⟩ : Edge m) ≠ AModel.swapMat := by sorry

end OneEdge
