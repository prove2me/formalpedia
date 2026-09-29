-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_chiral_trigonal
-- name    : LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_chiral_trigonal
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-27T16:02:41.670723+00:00
-- url     : https://prove2.me/theorems/dc118d05-311c-4fcf-a0b2-369341786c5b
-- title:
--   Chirality of the trigonal enantiomorphic space-group pairs
-- statement:
--   Throughout, $E=\mathbb R^3$, $G_1,\dots,G_{230}$ are the groups of the explicit catalogue `spaceGroupCatalog` (the group $G_n$ realises the space-group type with ITA number $n$, and the second member of each enantiomorphic pair is the image of the first under the point inversion $x\mapsto -x$; see the definition `SpaceGroupCatalog`), and $G\sim_+G'$ means that some invertible affine map $\varphi$ of $E$ with $\det\varphi_{\mathrm{lin}}>0$ satisfies $\varphi G\varphi^{-1}=G'$ (`AffOPEquivalent`).
--
--   For each of the three enantiomorphic pairs $(n,n')$ among $(144,145)$ ($P3_{1}$ / $P3_{2}$), $(151,153)$ ($P3_{1}12$ / $P3_{2}12$), $(152,154)$ ($P3_{1}21$ / $P3_{2}21$),
--
--   $$G_n\not\sim_+G_{n'}.$$
--
--   (In Lean the catalogue is indexed from $0$, so $G_n$ is `spaceGroupCatalog (n-1)`.) These are the trigonal cases of the statement that the eleven enantiomorphic pairs of space-group types are chiral, i.e. that the members of a pair are mirror images of each other but are not related by any orientation-preserving affine map.
-- source:
--   International Tables for Crystallography, Vol. A (T. Hahn, ed.), Section 1.4 and Table 1.4.1 (the 11 enantiomorphic pairs of space-group types); classification due to E. S. Fedorov (1891) and A. Schoenflies (1891).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem
namespace SpaceGroupCatalog

theorem spaceGroupCatalog_chiral_trigonal :
    ¬ AffOPEquivalent (spaceGroupCatalog 143) (spaceGroupCatalog 144) ∧
      ¬ AffOPEquivalent (spaceGroupCatalog 150) (spaceGroupCatalog 152) ∧
      ¬ AffOPEquivalent (spaceGroupCatalog 151) (spaceGroupCatalog 153) := by
  sorry

end SpaceGroupCatalog
end SpaceGroupsProblem
end Geometry
end LeanEval
