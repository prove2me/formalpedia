-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_exists_minimalInvariantData_of_counterexample
-- name    : OAI.ReflexiveFixedPoints.exists_minimalInvariantData_of_counterexample
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:03:19.996016+00:00
-- url     : https://prove2.me/theorems/a2920f0e-b5fb-4e7c-98aa-7447fd383af4
-- title:
--   A fixed-point-free map yields minimal invariant data
-- statement:
--   Let $X$ be a canonically reflexive real normed space, $C\subseteq X$ nonempty, closed, bounded and convex, and $F:C\to C$ nonexpansive without fixed points. Then there is minimal invariant data with $K\subseteq C$: a nonempty closed bounded convex separable weakly compact set $K$ and a nonexpansive fixed-point-free $T:K\to K$ (a restriction of $F$) such that
--   $$
--   \text{no nonempty closed convex }T\text{-invariant }s\subsetneq K .
--   $$
--
--   Counterexamples can always be made minimal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/MinimalInvariant.lean#L51-L123

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness

open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.ReflexiveFixedPoints.exists_minimalInvariantData_of_counterexample
    (hX : CanonicallyReflexive X) {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C) (hF : LipschitzWith 1 F) (hno : ∀ x : C, F x ≠ x) :
    ∃ D : MinimalInvariantData (X := X), D.K ⊆ C := by sorry
