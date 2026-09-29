-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_enantiomorphs_chiral
-- name    : LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_enantiomorphs_chiral
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-27T11:05:57.534616+00:00
-- url     : https://prove2.me/theorems/ab439611-17a5-4a70-8244-57f0350d80c1
-- title:
--   The 11 enantiomorphic pairs are not orientation-preserving affinely equivalent
-- statement:
--   Throughout, $E=\mathbb R^3$ with its Euclidean metric, $G_1,\dots,G_{230}$ denote the groups of the explicit catalogue `spaceGroupCatalog` (the group $G_n$ realises the space-group type with ITA number $n$; see the definition `SpaceGroupCatalog`), $G\sim G'$ means that some invertible affine map $\varphi$ of $E$ satisfies $\varphi G\varphi^{-1}=G'$, and $G\sim_+G'$ means that such a $\varphi$ exists with $\det\varphi_{\mathrm{lin}}>0$.
--
--   For each of the $11$ enantiomorphic pairs $(n,n')\in\{(76,78),(91,95),(92,96),(144,145),(151,153),(152,154),(169,170),(171,172),(178,179),(180,181),(212,213)\}$,
--
--   $$G_n\not\sim_+ G_{n'} .$$
--
--   That is, although the two members of a pair are mirror images of each other (hence affinely equivalent), no affine map with positive determinant conjugates one onto the other: these space groups are chiral. This is exactly why the count of orientation-preserving affine classes ($230$) exceeds the count of affine classes ($219$) by $11$.
-- source:
--   International Tables for Crystallography, Vol. A (T. Hahn, ed.), Section 1.4 and Table 1.4.1 (230 space-group types, 219 affine classes, 11 enantiomorphic pairs, 65 Sohncke types); classification due to E. S. Fedorov (1891) and A. Schoenflies (1891). Catalogue data: standard settings of ITA Vol. A via Hall symbols (S. R. Hall, Acta Cryst. A37 (1981) 517-525).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem
namespace SpaceGroupCatalog

theorem spaceGroupCatalog_enantiomorphs_chiral :
    ∀ p ∈ enantiomorphicPairs, ¬ AffOPEquivalent (spaceGroupCatalog p.1) (spaceGroupCatalog p.2) := by
  sorry

end SpaceGroupCatalog
end SpaceGroupsProblem
end Geometry
end LeanEval
