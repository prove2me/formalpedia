-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_exists_unit_ball_net
-- name    : OAI.SubsphereRegression.exists_unit_ball_net
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:06:27.762211+00:00
-- url     : https://prove2.me/theorems/efaf0d3a-4b77-4ce5-bf8d-599393ce7956
-- title:
--   The unit ball has an $r$-net of at most $(3/r)^{\dim E}$ points
-- statement:
--   Let $E$ be a finite-dimensional real normed space of dimension $d=\dim E$, with its Borel $\sigma$-algebra, and let $0<r\le1$. Then there is a finite set $s\subseteq E$ of points of norm at most $1$ such that
--   $$|s|\le\left(\frac{3}{r}\right)^{d}\qquad\text{and}\qquad\forall x\in E:\ \|x\|\le1\ \Longrightarrow\ \exists y\in s:\ \|x-y\|\le r.$$
--   In words, the closed unit ball has an $r$-net consisting of at most $(3/r)^{d}$ of its own points.
--
--   This is the standard quantitative net of the unit ball, stated with explicit constants. It is the input for covering the part of a tube around an affine subspace that lies in the unit ball by few balls, and hence for bounding the mass that measures with a local mass bound give to such tubes.
--
--   **Formalization Note** The dimension is `Module.finrank ℝ E` and `dist x y = ‖x - y‖`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Geometry.lean#L233-L254

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.exists_unit_ball_net {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ r := by sorry
