-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_exists_unit_ball_net
-- name    : OAI.NoiselessRegression.exists_unit_ball_net
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:22:37.5047+00:00
-- url     : https://prove2.me/theorems/54cb9d41-e9f5-4d72-932b-11a80d830c2d
-- title:
--   The unit ball has an $r$-net of at most $(3/r)^{\dim E}$ points
-- statement:
--   Let $E$ be a finite-dimensional real normed space of dimension $n=\dim E$, and let $r$ be a real number with $0<r\le1$. Then there exists a finite set $S\subseteq E$ such that
--   $$
--   S\subseteq\bar B(0,1),\qquad |S|\le\Big(\frac{3}{r}\Big)^{n},\qquad\text{and}\qquad \forall x\in E:\ \|x\|\le1\ \Longrightarrow\ \exists\,y\in S\ \ \|x-y\|\le r .
--   $$
--   Here $\bar B(0,1)=\{x\in E:\|x\|\le1\}$ is the closed unit ball and $|S|$ is the number of elements of $S$.
--
--   So the closed unit ball can be covered by at most $(3/r)^{\dim E}$ closed balls of radius $r$ whose centers lie in the ball itself. This is the standard volumetric bound on covering numbers. It is used to cover thin tubes around affine subspaces by few balls, and, with $r=\tfrac12$, to compare the operator norm of a linear map with its maximum over a finite net.
--
--   **Formalization Note** The ambient context also fixes a Borel $\sigma$-algebra on $E$, which plays no role. The cardinality bound is stated in the reals as `(s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E`, and closeness is `dist x y ≤ r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Nets.lean#L140-L159

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.exists_unit_ball_net {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ r := by sorry
