-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Descent_adaptive_step
-- name    : OAI.ArnoldCounterexample.Descent.adaptive_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:21:31.015741+00:00
-- url     : https://prove2.me/theorems/487829e5-6635-49d9-9e69-69d94e11ec6d
-- title:
--   An infinitesimal descent rate $S$ gives a uniform discrete descent step $c\,S$ on a compact set
-- statement:
--   Let $E$ be a real normed space, $K\subseteq E$ compact, and $\Phi:\mathbb{R}\times E\to\mathbb{R}$ smooth. Let $S:E\to\mathbb{R}$ be continuous with $S\ge0$ on $K$, and assume that for $z\in K$ the time derivative at $0$ is $-S(z)$:
--   $$
--   \partial_t\Phi(0,z)=-S(z).
--   $$
--   Then there is $c>0$ such that for every $z\in K$:
--   $$
--   0\le c\,S(z)\le1,\qquad \Phi\bigl(c\,S(z),z\bigr)\le\Phi(0,z),
--   $$
--   and if $S(z)\ne0$ the inequality is strict.
--
--   The step $cS(z)$ adapts to the descent rate, so it works even where $S$ vanishes to high order. This turns a smooth deformation that decreases a function to first order into an actual discrete map that does not increase it and strictly decreases it wherever $S\neq0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Descent.lean#L20-L87

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension

open OAI OAI.ArnoldCounterexample
universe uE uX
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Set
open scoped ContDiff
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.ArnoldCounterexample.Descent.adaptive_step {K : Set E} (hK : IsCompact K)
    (Φ : ℝ × E → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (S : E → ℝ) (hS : Continuous S)
    (hSnon : ∀ z ∈ K, 0 ≤ S z)
    (hd0 : ∀ z ∈ K, fderiv ℝ Φ (0, z) (1, 0) = -S z) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K,
      0 ≤ c * S z ∧ c * S z ≤ 1 ∧
      Φ (c * S z, z) ≤ Φ (0, z) ∧
      (S z ≠ 0 → Φ (c * S z, z) < Φ (0, z)) := by sorry
