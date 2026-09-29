-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_affine_irredundant
-- name    : LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_affine_irredundant
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-27T11:05:50.199455+00:00
-- url     : https://prove2.me/theorems/7cbc6c07-2771-4710-bf34-7611ac3f723a
-- title:
--   The 219 affine-class representatives are pairwise affinely inequivalent
-- statement:
--   Throughout, $E=\mathbb R^3$ with its Euclidean metric, $G_1,\dots,G_{230}$ denote the groups of the explicit catalogue `spaceGroupCatalog` (the group $G_n$ realises the space-group type with ITA number $n$; see the definition `SpaceGroupCatalog`), $G\sim G'$ means that some invertible affine map $\varphi$ of $E$ satisfies $\varphi G\varphi^{-1}=G'$, and $G\sim_+G'$ means that such a $\varphi$ exists with $\det\varphi_{\mathrm{lin}}>0$.
--
--   Let $n_1<\dots<n_{219}$ be the ITA numbers other than the second members $78,95,96,145,153,154,170,172,179,181,213$ of the enantiomorphic pairs. Then
--
--   $$G_{n_k}\sim G_{n_l}\ \Longrightarrow\ k=l .$$
--
--   In other words, the $219$ affine space-group types are pairwise distinct: no invertible affine map (of either orientation) conjugates two of these groups onto each other. Together with completeness, this gives the count of $219$ affine classes.
--
--   **Formalization note.** The list $n_1,\dots,n_{219}$ is `affineRepIndex`.
-- source:
--   International Tables for Crystallography, Vol. A (T. Hahn, ed.), Section 1.4 and Table 1.4.1 (230 space-group types, 219 affine classes, 11 enantiomorphic pairs, 65 Sohncke types); classification due to E. S. Fedorov (1891) and A. Schoenflies (1891). Catalogue data: standard settings of ITA Vol. A via Hall symbols (S. R. Hall, Acta Cryst. A37 (1981) 517-525).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem
namespace SpaceGroupCatalog

theorem spaceGroupCatalog_affine_irredundant :
    ∀ k l : Fin 219,
      AffinelyEquivalent (spaceGroupCatalog (affineRepIndex k)) (spaceGroupCatalog (affineRepIndex l)) →
        k = l := by
  sorry

end SpaceGroupCatalog
end SpaceGroupsProblem
end Geometry
end LeanEval
