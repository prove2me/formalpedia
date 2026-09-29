-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_affine_cover
-- name    : LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_affine_cover
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-27T11:05:42.968303+00:00
-- url     : https://prove2.me/theorems/1b1192dd-24ff-4b37-9a57-10b0dbdb15be
-- title:
--   Each catalogue group is affinely equivalent to its affine-class representative
-- statement:
--   Throughout, $E=\mathbb R^3$ with its Euclidean metric, $G_1,\dots,G_{230}$ denote the groups of the explicit catalogue `spaceGroupCatalog` (the group $G_n$ realises the space-group type with ITA number $n$; see the definition `SpaceGroupCatalog`), $G\sim G'$ means that some invertible affine map $\varphi$ of $E$ satisfies $\varphi G\varphi^{-1}=G'$, and $G\sim_+G'$ means that such a $\varphi$ exists with $\det\varphi_{\mathrm{lin}}>0$.
--
--   Let $r(n)$ be the representative of the affine class of type $n$: $r(n)=n$, except for the second member $n'$ of each enantiomorphic pair $(n,n')$, for which $r(n')=n$. Then
--
--   $$G_{r(n)}\sim G_n\qquad\text{for all } n.$$
--
--   This is the easy half of the passage from $230$ to $219$: enantiomorphic partners are mirror images of each other, hence conjugate under an orientation-reversing affine map.
--
--   **Formalization note.** $r$ is encoded by `affineRepIndex (affineClassIndex i)`.
-- source:
--   International Tables for Crystallography, Vol. A (T. Hahn, ed.), Section 1.4 and Table 1.4.1 (230 space-group types, 219 affine classes, 11 enantiomorphic pairs, 65 Sohncke types); classification due to E. S. Fedorov (1891) and A. Schoenflies (1891). Catalogue data: standard settings of ITA Vol. A via Hall symbols (S. R. Hall, Acta Cryst. A37 (1981) 517-525).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem
namespace SpaceGroupCatalog

theorem spaceGroupCatalog_affine_cover :
    ∀ i : Fin 230,
      AffinelyEquivalent (spaceGroupCatalog (affineRepIndex (affineClassIndex i)))
        (spaceGroupCatalog i) := by
  sorry

end SpaceGroupCatalog
end SpaceGroupsProblem
end Geometry
end LeanEval
