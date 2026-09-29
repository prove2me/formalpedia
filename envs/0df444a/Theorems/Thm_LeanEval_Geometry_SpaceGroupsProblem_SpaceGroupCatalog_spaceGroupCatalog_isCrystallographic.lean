-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_isCrystallographic
-- name    : LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_isCrystallographic
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-27T11:05:33.7999+00:00
-- url     : https://prove2.me/theorems/c2b000f4-15b8-4a45-b187-7616fb7d4915
-- title:
--   Every group of the space-group catalogue is crystallographic
-- statement:
--   Throughout, $E=\mathbb R^3$ with its Euclidean metric, $G_1,\dots,G_{230}$ denote the groups of the explicit catalogue `spaceGroupCatalog` (the group $G_n$ realises the space-group type with ITA number $n$; see the definition `SpaceGroupCatalog`), $G\sim G'$ means that some invertible affine map $\varphi$ of $E$ satisfies $\varphi G\varphi^{-1}=G'$, and $G\sim_+G'$ means that such a $\varphi$ exists with $\det\varphi_{\mathrm{lin}}>0$.
--
--   Each catalogue group is a crystallographic group in the sense of the LeanEval definitions: for all $n$,
--
--   $$G_n \text{ is discrete and contains translations by three linearly independent vectors.}$$
--
--   Here *discrete* means that for every $x\in E$ and $\varepsilon>0$ only finitely many $g\in G_n$ satisfy $\operatorname{dist}(gx,x)\le\varepsilon$. This certifies that the catalogue consists of genuine space groups, so that it can serve as a list of representatives in the classification.
-- source:
--   International Tables for Crystallography, Vol. A (T. Hahn, ed.), Section 1.4 and Table 1.4.1 (230 space-group types, 219 affine classes, 11 enantiomorphic pairs, 65 Sohncke types); classification due to E. S. Fedorov (1891) and A. Schoenflies (1891). Catalogue data: standard settings of ITA Vol. A via Hall symbols (S. R. Hall, Acta Cryst. A37 (1981) 517-525).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem
namespace SpaceGroupCatalog

theorem spaceGroupCatalog_isCrystallographic :
    ∀ i : Fin 230, IsCrystallographicGroup (spaceGroupCatalog i) := by
  sorry

end SpaceGroupCatalog
end SpaceGroupsProblem
end Geometry
end LeanEval
