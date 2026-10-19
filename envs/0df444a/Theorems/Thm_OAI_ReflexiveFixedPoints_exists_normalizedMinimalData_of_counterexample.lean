-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_exists_normalizedMinimalData_of_counterexample
-- name    : OAI.ReflexiveFixedPoints.exists_normalizedMinimalData_of_counterexample
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:04:55.91235+00:00
-- url     : https://prove2.me/theorems/24823598-9ee9-47be-a8ca-797f7dbbce92
-- title:
--   A fixed-point-free map yields normalized minimal data
-- statement:
--   Let $X$ be a canonically reflexive real normed space, $C$ nonempty, closed, bounded and convex, and $F:C\to C$ nonexpansive without fixed points. Then there are normalized minimal invariant data: a minimal invariant set $K$ for a fixed-point-free nonexpansive $T$, with
--   $$
--   \operatorname{diam}K=1,
--   $$
--   a dense sequence, a metrizable weak topology on $K$, and a weakly compact difference ball $\{x\in\overline{\mathrm{span}}(K-K):\|x\|\le1\}$.
--
--   This is the starting point of the contradiction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/Reduction.lean#L27-L49

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric

open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.ReflexiveFixedPoints.exists_normalizedMinimalData_of_counterexample
    (hX : CanonicallyReflexive X) {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C) (hF : LipschitzWith 1 F) (hno : ∀ x : C, F x ≠ x) :
    Nonempty (NormalizedMinimalData (X := X)) := by sorry
