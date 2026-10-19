-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_exists_separable_invariant_subset
-- name    : OAI.ReflexiveFixedPoints.exists_separable_invariant_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:02:16.996023+00:00
-- url     : https://prove2.me/theorems/e61e214d-a8f1-4297-8242-c225b4e497ed
-- title:
--   Separable invariant subsets of a nonexpansive map
-- statement:
--   Let $C$ be a nonempty closed bounded convex subset of a real normed space $X$ and $F:C\to C$ nonexpansive. Then there is a nonempty, closed, bounded, convex, separable $S\subseteq C$ with
--   $$
--   F(C\cap S)\subseteq S .
--   $$
--
--   Every counterexample to the fixed point property can be restricted to a separable one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/SeparableInvariant.lean#L33-L110

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic

open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.ReflexiveFixedPoints.exists_separable_invariant_subset {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C)
    (hconvex : Convex ℝ C) (F : C → C) (hF : LipschitzWith 1 F) :
    ∃ S : Set X, S ⊆ C ∧ S.Nonempty ∧ IsClosed S ∧ Bornology.IsBounded S ∧
      Convex ℝ S ∧ IsSeparable S ∧ InvariantSubset C F S := by sorry
