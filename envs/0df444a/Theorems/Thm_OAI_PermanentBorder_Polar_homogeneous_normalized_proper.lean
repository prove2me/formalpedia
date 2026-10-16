-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_homogeneous_normalized_proper
-- name    : OAI.PermanentBorder.Polar.homogeneous_normalized_proper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:52:05.677737+00:00
-- url     : https://prove2.me/theorems/3a4d8c0d-2a1e-48af-b21a-e9d6ea34e83b
-- title:
--   Affine normalisation of a closed family of cones without points at infinity is proper over the parameters
-- statement:
--   Let $T$ be a topological space and let $V$ be a complex normed space in which closed balls are compact (a proper space; for example a finite-dimensional one). For each parameter $t\in T$ let $H(t,\cdot)$ be a condition on vectors of $V$ and $L_t:V\to\mathbb{C}$ a linear functional, and assume:
--
--   1. the incidence set $\{(t,y)\in T\times V:\ H(t,y)\}$ is closed in $T\times V$;
--   2. each $H(t,\cdot)$ defines a cone: $H(t,y)$ implies $H(t,cy)$ for every $c\in\mathbb{C}$;
--   3. the map $(t,y)\mapsto L_t(y)$ is continuous on $T\times V$;
--   4. no nonzero vector of the cone lies on the hyperplane $L_t=0$: if $H(t,y)$ and $L_t(y)=0$, then $y=0$.
--
--   Let $Z=\{(t,y)\in T\times V:\ H(t,y)\ \text{and}\ L_t(y)=1\}$, the cones cut by the affine hyperplanes $L_t=1$, with the subspace topology. Then the projection
--
--   $$
--   \pi:Z\to T,\qquad\pi(t,y)=t,
--   $$
--
--   is a proper map.
--
--   For a parametrised system of homogeneous polynomial equations, $Z$ is the set of its solutions normalised by $L_t=1$, and condition 4 says that no projective solution lies at infinity with respect to $L_t$. Properness of $\pi$ then means that normalised solutions cannot escape to infinity as the parameter moves; combined with a local homeomorphism property, this keeps the number of solutions constant along connected parameter sets.
--
--   **Formalization Note** The condition is a predicate `H : T → V → Prop`, the functionals are `L : T → V →ₗ[ℂ] ℂ` (continuity is required jointly in $(t,y)$), $V$ carries the instance `ProperSpace V`, $Z$ is a subtype of `T × V`, and properness is Mathlib's `IsProperMap`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RegularSections.lean#L421-L466

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections

open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open Topology Set

theorem OAI.PermanentBorder.Polar.homogeneous_normalized_proper {T V : Type*} [TopologicalSpace T]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [ProperSpace V]
    (H : T → V → Prop) (hH : IsClosed {z : T × V | H z.1 z.2})
    (hsmul : ∀ t y (c : ℂ), H t y → H t (c • y))
    (L : T → V →ₗ[ℂ] ℂ) (hL : Continuous (fun z : T × V => L z.1 z.2))
    (hno : ∀ t y, H t y → L t y = 0 → y = 0) :
    IsProperMap (fun z : {z : T × V // H z.1 z.2 ∧ L z.1 z.2 = 1} => z.val.1) := by sorry
