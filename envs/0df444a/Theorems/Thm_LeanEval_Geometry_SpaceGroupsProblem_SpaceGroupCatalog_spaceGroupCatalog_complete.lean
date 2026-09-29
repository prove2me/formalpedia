-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_complete
-- name    : LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_complete
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-27T11:06:02.630617+00:00
-- url     : https://prove2.me/theorems/f0fcb577-6809-4d2c-8f92-e66b68aa82e3
-- title:
--   Completeness of the space-group catalogue (Fedorov–Schoenflies)
-- statement:
--   Throughout, $E=\mathbb R^3$ with its Euclidean metric, $G_1,\dots,G_{230}$ denote the groups of the explicit catalogue `spaceGroupCatalog` (the group $G_n$ realises the space-group type with ITA number $n$; see the definition `SpaceGroupCatalog`), $G\sim G'$ means that some invertible affine map $\varphi$ of $E$ satisfies $\varphi G\varphi^{-1}=G'$, and $G\sim_+G'$ means that such a $\varphi$ exists with $\det\varphi_{\mathrm{lin}}>0$.
--
--   Every crystallographic group of $\mathbb R^3$ is orientation-preserving affinely equivalent to a member of the catalogue:
--
--   $$\forall\,G\ \text{crystallographic},\quad \exists\, n\in\{1,\dots,230\}:\ G_n\sim_+ G.$$
--
--   This is the existence half of the classification of three-dimensional space groups: every space group belongs to one of the $230$ types tabulated in the International Tables. It is the deep part of the theorem (Bieberbach's structure theory, the $73$ arithmetic classes of finite subgroups of $\mathrm{GL}_3(\mathbb Z)$, and the computation of the non-symmorphic extensions).
-- source:
--   International Tables for Crystallography, Vol. A (T. Hahn, ed.), Section 1.4 and Table 1.4.1 (230 space-group types, 219 affine classes, 11 enantiomorphic pairs, 65 Sohncke types); classification due to E. S. Fedorov (1891) and A. Schoenflies (1891). Catalogue data: standard settings of ITA Vol. A via Hall symbols (S. R. Hall, Acta Cryst. A37 (1981) 517-525).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem
namespace SpaceGroupCatalog

theorem spaceGroupCatalog_complete :
    ∀ G : CrystallographicGroup 3, ∃ i : Fin 230, AffOPEquivalent (spaceGroupCatalog i) G.1 := by
  sorry

end SpaceGroupCatalog
end SpaceGroupsProblem
end Geometry
end LeanEval
