-- Prove2me | Theorems.Thm_LorentzFactor_boost_mul_boost
-- name    : LorentzFactor.boost_mul_boost
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:54:33.945708+00:00
-- url     : https://prove2.me/theorems/d380c941-881a-488f-a74c-fa2d337512a5
-- title:
--   Composition of Lorentz boosts is a boost with relativistically added velocity
-- statement:
--   **Goal of the mission.** Let $\beta_1, \beta_2$ be subluminal velocity ratios, $|\beta_1| < 1$ and $|\beta_2| < 1$, and let
--
--   $$B(\beta) = \begin{pmatrix} \gamma(\beta) & -\gamma(\beta)\beta \\ -\gamma(\beta)\beta & \gamma(\beta) \end{pmatrix}$$
--
--   be the Lorentz boost along the $x$-axis acting on $(t, x)$, in units $c = 1$. Then the composition of two boosts is again a boost, and its velocity is the relativistic sum of the two velocities:
--
--   $$B(\beta_1)B(\beta_2) = B\!\left(\frac{\beta_1 + \beta_2}{1 + \beta_1\beta_2}\right),$$
--
--   the composed velocity is again subluminal, and the Lorentz factors multiply according to
--
--   $$\gamma(\beta_1 \oplus \beta_2) = \gamma(\beta_1)\gamma(\beta_2)(1 + \beta_1\beta_2).$$
--
--   This is the statement that the boosts of the source article form a one-parameter group under relativistic velocity addition — the group-theoretic content behind the additivity of rapidity, and the composition law from which time dilation and length contraction are read off.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem boost_mul_boost (β₁ β₂ : ℝ) (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    boost β₁ * boost β₂ = boost (velAdd β₁ β₂) ∧
      gamma (velAdd β₁ β₂) = gamma β₁ * gamma β₂ * (1 + β₁ * β₂) ∧
      |velAdd β₁ β₂| < 1 := by sorry

end LorentzFactor
