-- Prove2me | Theorems.Thm_OAI_ThreeManifold_PassageDynamics_scalar_reflection
-- name    : OAI.ThreeManifold.PassageDynamics.scalar_reflection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:32:17.90004+00:00
-- url     : https://prove2.me/theorems/98db50b7-382b-4f65-bd0a-82527bca1e46
-- title:
--   Reflection symmetry of solutions of $t^{\prime\prime} = -F(t)/2$ about a turning point
-- statement:
--   Let $F : \mathbb{R} \to \mathbb{R}$ be a $C^\infty$ function, let $t, v : \mathbb{R} \to \mathbb{R}$, and let $a < c < b$ be real numbers with $a + b = 2c$ (so $c$ is the midpoint of $[a,b]$). Suppose that at every point $s \in [a,b]$ the functions are differentiable with
--   $$
--   t'(s) = v(s), \qquad v'(s) = -\tfrac12 F\big(t(s)\big),
--   $$
--   and that $v(c) = 0$. Then for every $s \in [a,b]$,
--   $$
--   t(2c - s) = t(s) \qquad\text{and}\qquad v(2c - s) = -v(s).
--   $$
--
--   This is the time-reversal symmetry of the conservative one-dimensional motion $t'' = -F(t)/2$: a trajectory whose velocity vanishes at time $c$ is symmetric about $c$. It is used to show that a passage of a geodesic into the neck and back is symmetric about its turning time.
--
--   **Formalization Note** The derivative hypotheses are two-sided derivatives (`HasDerivAt`) at every point of the closed interval $[a,b]$, so $t$ and $v$ are in particular defined and differentiable slightly beyond the endpoints.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L1031-L1050

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

open OAI OAI.ThreeManifold OAI.ThreeManifold.PassageDynamics
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff

theorem OAI.ThreeManifold.PassageDynamics.scalar_reflection {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b) (hab : a + b = 2 * c)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F₁ (t s) / 2) s)
    (hvc : v c = 0) :
    ∀ s ∈ Icc a b, t (2 * c - s) = t s ∧ v (2 * c - s) = -v s := by sorry
