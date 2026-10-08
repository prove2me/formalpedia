-- Prove2me | Theorems.Thm_HryniewiczCriterion_positive_polar_angle_derivative
-- name    : HryniewiczCriterion.positive_polar_angle_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T20:59:34.785986+00:00
-- url     : https://prove2.me/theorems/6e326711-f19c-45d5-b0a3-7d305215afee
-- title:
--   Angular derivative of the positive polar action of a determinant-one plane matrix
-- statement:
--   Let $A\in\mathrm{SL}(2,\mathbb R)$ and write $v(u)=(\cos u,\sin u)$. Suppose $\theta:\mathbb R\to\mathbb R$ is continuous and for every $u$ there exists $a>0$ with $Av(u)=a\,v(\theta(u))$. If $s\in\mathbb R$ and $r>0$ satisfy $Av(s)=r\,v(\theta(s))$, then $\theta$ is differentiable at $s$ and
--   $$\theta'(s)=\frac1{r^2}.$$
--   This states the angular differentiation identity used in the forward implication of Hryniewicz's Lemma 2.1. It depends only on the endpoint linear map and a continuous positive polar angle, and applies even when differentiability of the angle was not assumed.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, https://arxiv.org/abs/1105.2077, Section 2.1.1, Lemma 2.1, p. 6, identity det φ(1) = r(1,s)^2 θ_s(1,s). This extracts the angular derivative step for an arbitrary determinant-one endpoint matrix.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

open HryniewiczCriterion Filter Topology
set_option maxHeartbeats 800000

theorem HryniewiczCriterion.positive_polar_angle_derivative
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det = 1)
    (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hp : ∀ u, ∃ r : ℝ, 0 < r ∧
      A.mulVec (rotationVector u) = r • rotationVector (θ u))
    (s r : ℝ) (hr : 0 < r)
    (hs : A.mulVec (rotationVector s) = r • rotationVector (θ s)) :
    HasDerivAt θ (1 / r^2) s := by sorry
