-- Prove2me | Theorems.Thm_Monod_noFreeSubgroupOfRankTwo_Hpp
-- name    : Monod.noFreeSubgroupOfRankTwo_Hpp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T13:11:47.834521+00:00
-- url     : https://prove2.me/theorems/47fdd12e-3459-44c6-b420-7d62383c8517
-- title:
--   Theorem 2 — H, and hence every H(A), has no non-abelian free subgroup
-- statement:
--   $H$ contains no free subgroup of rank two: no homomorphism from the free group on two generators into $H$ is injective. The same holds for $H(A)$, for every subring $A$ of $\mathbf{R}$.
--
--   **Formalization Note.** A group has a non-abelian free subgroup exactly when it has a free subgroup of rank two; `Chou.NoFreeSubgroupOfRankTwo` is the published definition.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 1, Theorem 2

import Mathlib
import Definitions.Def_Chou_Classes
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem noFreeSubgroupOfRankTwo_Hpp :
    Chou.NoFreeSubgroupOfRankTwo Hpp ∧ ∀ A : Subring ℝ, Chou.NoFreeSubgroupOfRankTwo (H A) := by
  sorry

end Monod
