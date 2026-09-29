-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups
-- name    : LeanEval.Geometry.SpaceGroupsProblem.space_groups
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-06T02:38:38.164396+00:00
-- url     : https://prove2.me/theorems/da34f26b-242d-4ff6-8a63-ccca1767d130
-- title:
--   230 space groups: the exact 230, 219, and 65 counts
-- statement:
--   Consider all subgroups of the affine isometry group of $\mathbb R^3$ satisfying the finite-displacement discreteness condition and containing translations by three linearly independent vectors, as specified in the accompanying definitions. Write $C_{\mathrm{OP}}(3)$ for their number of classes under conjugation by affine maps of positive linear determinant, $C(3)$ for the number under arbitrary invertible affine conjugacy, and $C_{\mathrm{OP,only}}(3)$ for the number under the first relation after restricting to groups whose every isometry has positive linear determinant. Then the single goal is the conjunction
--
--   $$C_{\mathrm{OP}}(3)=230\quad\land\quad C(3)=219\quad\land\quad C_{\mathrm{OP,only}}(3)=65.$$
--
--   The third number counts the Sohncke subfamily. All three numbers are cardinalities in the extended natural numbers of sets of class subsets, so the equalities assert finiteness as well as exact values. This is the unchanged LeanEval benchmark assertion, not just the length of a list of named space groups.
--
--   **Formalization Note.** The imported definition bundle preserves the source declarations verbatim. The declaration is an unproved statement placeholder, not a submitted proof. It is the sole theorem item; there are no milestones or auxiliary theorem items.
-- source:
--   LeanEval v1, statement revision 1, problem space_groups_230; LeanEval/Geometry/SpaceGroups.lean, LeanEval.Geometry.SpaceGroupsProblem.space_groups, repository commit 296b7491ec989d21bcf8636a9a69231a1e5d1d25: https://github.com/leanprover/lean-eval/blob/296b7491ec989d21bcf8636a9a69231a1e5d1d25/LeanEval/Geometry/SpaceGroups.lean . Metadata: manifests/problems/space_groups_230.toml at the same commit. Background: Oliver Knill, Some Fundamental Theorems in Mathematics, section 94 (Crystallography), printed p. 41, version last updated June 25, 2023, https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf . The exact LeanEval definitions, not the background prose alone, govern this target.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem space_groups :
    crystallographicCountOP 3 = 230 ∧
      crystallographicCount 3 = 219 ∧
        crystallographicCountOPOnly 3 = 65 := by
  sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
