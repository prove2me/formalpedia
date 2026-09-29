-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_euclideanGroup_linPart_extension
-- name    : LeanEval.Geometry.SpaceGroupsProblem.euclideanGroup_linPart_extension
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T08:24:03.746264+00:00
-- url     : https://prove2.me/theorems/d0eda4c3-491f-4fc2-b5d0-d1a82dfcfaf5
-- title:
--   A group of Euclidean isometries is an extension of its point group by its translations
-- statement:
--   Let $G$ be a subgroup of the Euclidean motion group $E_d$ of $\mathbb{R}^d$. Every isometry $g$ decomposes as $g(x)=\mathrm{lin}(g)(x)+g(0)$ with linear part $\mathrm{lin}(g)\in O(d)$.
--
--   The theorem asserts that $\mathrm{lin}$ is a group homomorphism $G\to O(d)$ with the following properties:
--
--   1. its image is the point group $P(G)$;
--   2. its kernel consists exactly of those elements of $G$ that are translations $x\mapsto x+v$;
--   3. the induced map on the quotient is a group isomorphism
--
--   $$G/\ker(\mathrm{lin})\;\cong\;P(G).$$
--
--   Equivalently, $G$ is an extension
--
--   $$1\longrightarrow T(G)\longrightarrow G\longrightarrow P(G)\longrightarrow 1$$
--
--   of its point group by its group of translations. For a crystallographic group the kernel is a lattice of rank $d$ and the quotient is finite; this exact sequence is the frame in which space groups are classified by cohomological extension data.
-- source:
--   L. S. Charlap, Bieberbach Groups and Flat Manifolds, Springer 1986, Chapter I, Section 1 (the exact sequence 1 -> translations -> G -> point group -> 1).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem euclideanGroup_linPart_extension {d : ℕ} (G : Subgroup (EuclideanIsom d)) :
    ∃ f : G →* (E d ≃ₗᵢ[ℝ] E d),
      (∀ g : G, f g = linPart g.1) ∧
      f.range = pointGroup G ∧
      (∀ g : G, g ∈ f.ker ↔ ∃ v, IsTranslationBy g.1 v) ∧
      Nonempty ((G ⧸ f.ker) ≃* pointGroup G) := by sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
