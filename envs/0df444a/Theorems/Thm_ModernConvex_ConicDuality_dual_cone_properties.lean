-- Prove2me | Theorems.Thm_ModernConvex_ConicDuality_dual_cone_properties
-- name    : ModernConvex.ConicDuality.dual_cone_properties
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:28.639737+00:00
-- url     : https://prove2.me/theorems/f921e06f-c06a-4ede-af5a-2d14cefd5daf
-- title:
--   Theorem 2.3.1 — properties of the dual cone
-- statement:
--   Let $K \subset \mathbb R^m$ be a nonempty set and let
--   $$K_* = \{\lambda \in \mathbb R^m : \lambda^Ta \ge 0 \ \ \forall a \in K\}$$
--   be its dual cone. Then:
--
--   1. $K_*$ is a closed convex cone.
--   2. If $\operatorname{int} K \ne \emptyset$, then $K_*$ is pointed.
--   3. If $K$ is a closed convex pointed cone, then $\operatorname{int} K_* \ne \emptyset$.
--   4. If $K$ is a closed convex cone, then so is $K_*$, and the cone dual to $K_*$ is $K$ itself: $(K_*)_* = K$.
--
--   Here a convex cone is a nonempty set closed under addition and under multiplication by nonnegative reals, and it is pointed if it contains no pair $a, -a$ with $a \ne 0$. The theorem justifies the name "dual cone" and is what makes the dual of a conic problem over a good cone again a conic problem over a good cone.
--
--   **Formalization Note** Vectors are `Fin m → ℝ`; "convex cone", "pointed" and $K_*$ are the definitions `IsConvexCone`, `IsPointedSet`, `dualCone` of the mission's definition file, and closedness and interior are taken in the usual (Euclidean) topology.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 52, Theorem 2.3.1

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

namespace ModernConvex.ConicDuality

/-- Ben-Tal–Nemirovski, Theorem 2.3.1 (properties of the dual cone), p. 52. For a nonempty set
`K ⊂ ℝᵐ` and `K∗ = {λ | λᵀa ≥ 0 ∀ a ∈ K}`:
(i) `K∗` is a closed convex cone; (ii) if `int K ≠ ∅` then `K∗` is pointed;
(iii) if `K` is a closed convex pointed cone then `int K∗ ≠ ∅`;
(iv) if `K` is a closed convex cone then so is `K∗`, and `(K∗)∗ = K`. -/
theorem dual_cone_properties {m : ℕ} (K : Set (Fin m → ℝ)) (hK : K.Nonempty) :
    -- (i)
    (IsConvexCone (dualCone K) ∧ IsClosed (dualCone K)) ∧
    -- (ii)
    ((interior K).Nonempty → IsPointedSet (dualCone K)) ∧
    -- (iii)
    (IsConvexCone K ∧ IsClosed K ∧ IsPointedSet K → (interior (dualCone K)).Nonempty) ∧
    -- (iv)
    (IsConvexCone K ∧ IsClosed K →
      (IsConvexCone (dualCone K) ∧ IsClosed (dualCone K)) ∧ dualCone (dualCone K) = K) := by sorry

end ModernConvex.ConicDuality
