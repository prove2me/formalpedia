-- Prove2me | Theorems.Thm_MartinetReg_ConvexMin_exists_solution
-- name    : MartinetReg.ConvexMin.exists_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:45.449635+00:00
-- url     : https://prove2.me/theorems/a337a165-df18-4d72-b296-800e4ec9756b
-- title:
--   §4.1 — the convex problem (12) with bounded sublevel sets has a solution
-- statement:
--   Let $H$ be a real Hilbert space, $C\subseteq H$ a nonempty closed convex set, and $f:H\to\mathbb R$ convex and lower semicontinuous, such that $\{x\in C\mid f(x)\le a\}$ is bounded for every $a\in\mathbb R$. Then problem (12) has a solution: there is $\bar x\in C$ with
--   $$
--   f(\bar x)\le f(x)\qquad\text{for all } x\in C .
--   $$
--
--   This is the existence statement Martinet makes right after the hypotheses of §4.1 ("Ces hypothèses assurent l'existence d'une solution pour (12)"). It is used to make sense of "the solution set of (12)" in Théorème 3 and of "la solution unique" in Remarque 1.
--
--   **Formalization Note** The paper leaves $C\neq\emptyset$ implicit; the claim is false for $C=\emptyset$, so nonemptiness is a hypothesis (inside `Standing`).
-- source:
--   Martinet, Régularisation d'inéquations variationnelles par approximations successives, R.I.R.O. 4(R-3) (1970), p. 157, §4.1, after (12)

import Mathlib
import Definitions.Def_MartinetReg_ConvexMin_Setting

namespace MartinetReg.ConvexMin

/-- §4.1, p. 157: under the hypotheses of §4.1, problem (12) has a solution. -/
theorem exists_solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C) :
    (solSet f C).Nonempty := by sorry

end MartinetReg.ConvexMin
