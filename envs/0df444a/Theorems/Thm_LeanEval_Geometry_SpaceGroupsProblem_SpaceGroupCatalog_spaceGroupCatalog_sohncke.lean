-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_sohncke
-- name    : LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_sohncke
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-27T11:05:52.910479+00:00
-- url     : https://prove2.me/theorems/ee579098-92f8-4ac2-a3e1-3231ac9b88c0
-- title:
--   The 65 Sohncke groups of the catalogue
-- statement:
--   Throughout, $E=\mathbb R^3$ with its Euclidean metric, $G_1,\dots,G_{230}$ denote the groups of the explicit catalogue `spaceGroupCatalog` (the group $G_n$ realises the space-group type with ITA number $n$; see the definition `SpaceGroupCatalog`), $G\sim G'$ means that some invertible affine map $\varphi$ of $E$ satisfies $\varphi G\varphi^{-1}=G'$, and $G\sim_+G'$ means that such a $\varphi$ exists with $\det\varphi_{\mathrm{lin}}>0$.
--
--   Let $S\subset\{1,\dots,230\}$ be the set of the $65$ Sohncke types (ITA numbers $1,3,4,5,16$–$24,75$–$80,89$–$98,143$–$146,149$–$155,168$–$173,177$–$182,195$–$199,207$–$214$). Then the listing of $S$ is injective, and for every $n$,
--
--   $$\bigl(\forall g\in G_n:\ \det g_{\mathrm{lin}}>0\bigr)\iff n\in S .$$
--
--   So exactly $65$ catalogue groups consist of orientation-preserving isometries only.
--
--   **Formalization note.** $S$ is given by the injective map `sohnckeIndex : Fin 65 → Fin 230`.
-- source:
--   International Tables for Crystallography, Vol. A (T. Hahn, ed.), Section 1.4 and Table 1.4.1 (230 space-group types, 219 affine classes, 11 enantiomorphic pairs, 65 Sohncke types); classification due to E. S. Fedorov (1891) and A. Schoenflies (1891). Catalogue data: standard settings of ITA Vol. A via Hall symbols (S. R. Hall, Acta Cryst. A37 (1981) 517-525).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem
namespace SpaceGroupCatalog

theorem spaceGroupCatalog_sohncke :
    Function.Injective sohnckeIndex ∧
      ∀ i : Fin 230, (∀ g, g ∈ spaceGroupCatalog i → IsOrientationPreservingIsom g) ↔
        ∃ k : Fin 65, sohnckeIndex k = i := by
  sorry

end SpaceGroupCatalog
end SpaceGroupsProblem
end Geometry
end LeanEval
