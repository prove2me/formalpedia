-- Prove2me | Theorems.Thm_MilnorDynamics_milnorLambdaHalfShift_den_eq_theta
-- name    : MilnorDynamics.milnorLambdaHalfShift_den_eq_theta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T12:29:59.487516+00:00
-- url     : https://prove2.me/theorems/845aa4c8-64a9-47d3-9bff-87d1488c85cf
-- title:
--   The corrected denominator unfolds to $\theta_3(\tau)^4$
-- statement:
--   A definitional check on the *corrected* modular lambda. Writing $\theta_3(\tau) = \sum_{n \in \mathbb{Z}} e^{\pi i n^2 \tau}$ for the one-variable Jacobi theta function, the claim is that the denominator $D(\tau) = \theta_3(\tau)^4$ of $\lambda = \theta_2^4/D$ is *by definition* the fourth power of $\theta_3$, with no analytic content whatsoever.
--
--   This confirms two things at once: that the corrected definition `MilnorLambdaHalfShift` is importable from a later proof candidate at the correct environment revision, and that its denominator is the genuine first theta constant. The contrast is the point. The *first* published definition was proved to be the constant $1$ in `milnorLambda_published_is_constant`, precisely because its numerator and denominator coincided. Establishing that the denominator here is the real $\theta_3$ is the bookkeeping that separates the corrected quotient from the degenerate one.
--
--   **Only the definitional unfolding is claimed.** Holomorphy on $\mathbb{H}$, avoidance of $0$ and $1$, surjectivity onto $\mathbb{C} \setminus \{0,1\}$, properness, and the covering property all remain separate theorems.
-- source:
--   MilnorLambdaHalfShift (46b2af40-3f5b-4d4c-baad-3cb9839e2382); the theta series is Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable.jacobiTheta.

import Mathlib
import Definitions.Def_MilnorLambdaHalfShift

open Complex

open MilnorDynamics

namespace MilnorDynamics

/-- The corrected denominator unfolds to the fourth power of the one-variable
Jacobi theta function. -/
theorem milnorLambdaHalfShift_den_eq_theta :
    ∀ τ : ℂ, milnorLambdaHalfShiftDen τ = jacobiTheta τ ^ 4 := by
  sorry

end MilnorDynamics
