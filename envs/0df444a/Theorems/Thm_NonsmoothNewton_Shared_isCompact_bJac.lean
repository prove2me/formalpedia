-- Prove2me | Theorems.Thm_NonsmoothNewton_Shared_isCompact_bJac
-- name    : NonsmoothNewton.Shared.isCompact_bJac
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:42:20.567787+00:00
-- url     : https://prove2.me/theorems/f485ed74-88cd-4be1-b5b5-c50d91593930
-- title:
--   The B-Jacobian is compact at a point
-- statement:
--   Let $F : E \to G$ be locally Lipschitz at $x$, with $E$ and $G$ finite-dimensional real normed spaces, and let the B-limit set `bJac F x` be viewed as a subset of the finite-dimensional space of continuous linear maps $E \to_L \mathbb{R} G$.
--
--   Then `bJac F x` is a compact set.
--
--   **Formalization Note** Closedness comes from `bJac_mem_of_tendsto`: if $V_n \in \partial_B F(x)$ and $V_n \to V$ then $V \in \partial_B F(x)$, applied to the constant base-point sequence $x, x, x, \dots$. Boundedness comes from `exists_local_bJac_control`, which bounds the norm uniformly over a ball about $x$. Since the space of continuous linear maps between the two finite-dimensional spaces is finite-dimensional over the reals, it is a proper space (`FiniteDimensional.proper_real`), so `Metric.isCompact_iff_isClosed_bounded` gives compactness.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), Section 3, p. 354. Compactness of the B-limit set and of Clarke's generalized Jacobian at a point, via the finite-dimensional fact that the convex hull of a compact set is compact; the compactness input for the uniform local inverse-norm bound required by NonsmoothNewton.Local.prop_3_1.

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set

namespace NonsmoothNewton.Shared

/-- The B-limit set `bJac F x` is a compact subset of the space of continuous
linear maps.

Closedness is the sequential closed graph `bJac_mem_of_tendsto`: a convergent
sequence of elements of `bJac F x` converges into `bJac F x`, since a constant
base-point sequence is a special case. Boundedness is the local control
`exists_local_bJac_control`, which bounds `‖V‖` for `V ∈ bJac F x` by a single
constant. The space of continuous linear maps between the two finite-dimensional
spaces is itself finite-dimensional, hence proper, so Heine-Borel applies.

This is the compactness needed to turn pointwise invertibility of
`clarkeJac F x` into a uniform inverse bound over a neighbourhood. -/
theorem isCompact_bJac {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    IsCompact (bJac F x) := by sorry

end NonsmoothNewton.Shared
