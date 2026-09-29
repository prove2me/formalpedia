-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_chiral_tetragonal
-- name    : LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_chiral_tetragonal
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-27T16:02:42.622293+00:00
-- url     : https://prove2.me/theorems/e84bc8ff-8842-4ab1-bb87-628e132354f2
-- title:
--   Chirality of the tetragonal enantiomorphic space-group pairs
-- statement:
--   Throughout, $E=\mathbb R^3$, $G_1,\dots,G_{230}$ are the groups of the explicit catalogue `spaceGroupCatalog` (the group $G_n$ realises the space-group type with ITA number $n$, and the second member of each enantiomorphic pair is the image of the first under the point inversion $x\mapsto -x$; see the definition `SpaceGroupCatalog`), and $G\sim_+G'$ means that some invertible affine map $\varphi$ of $E$ with $\det\varphi_{\mathrm{lin}}>0$ satisfies $\varphi G\varphi^{-1}=G'$ (`AffOPEquivalent`).
--
--   For each of the three enantiomorphic pairs $(n,n')$ among $(76,78)$ ($P4_{1}$ / $P4_{3}$), $(91,95)$ ($P4_{1}22$ / $P4_{3}22$), $(92,96)$ ($P4_{1}2_{1}2$ / $P4_{3}2_{1}2$),
--
--   $$G_n\not\sim_+G_{n'}.$$
--
--   (In Lean the catalogue is indexed from $0$, so $G_n$ is `spaceGroupCatalog (n-1)`.) These are the tetragonal cases of the statement that the eleven enantiomorphic pairs of space-group types are chiral, i.e. that the members of a pair are mirror images of each other but are not related by any orientation-preserving affine map.
-- source:
--   International Tables for Crystallography, Vol. A (T. Hahn, ed.), Section 1.4 and Table 1.4.1 (the 11 enantiomorphic pairs of space-group types); classification due to E. S. Fedorov (1891) and A. Schoenflies (1891).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem
namespace SpaceGroupCatalog

theorem spaceGroupCatalog_chiral_tetragonal :
    ¬ AffOPEquivalent (spaceGroupCatalog 75) (spaceGroupCatalog 77) ∧
      ¬ AffOPEquivalent (spaceGroupCatalog 90) (spaceGroupCatalog 94) ∧
      ¬ AffOPEquivalent (spaceGroupCatalog 91) (spaceGroupCatalog 95) := by
  sorry

end SpaceGroupCatalog
end SpaceGroupsProblem
end Geometry
end LeanEval
