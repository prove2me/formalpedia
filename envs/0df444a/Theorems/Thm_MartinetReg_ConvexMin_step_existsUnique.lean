-- Prove2me | Theorems.Thm_MartinetReg_ConvexMin_step_existsUnique
-- name    : MartinetReg.ConvexMin.step_existsUnique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:57.473989+00:00
-- url     : https://prove2.me/theorems/b5cc3221-5d60-4659-9c6d-0fd3aaf94ac7
-- title:
--   §4.2, (13) — the regularized problem min (f(x) + ‖x − xⁿ‖² | x ∈ C) has a unique solution
-- statement:
--   Under the hypotheses of §4.1 ($H$ a real Hilbert space, $C\subseteq H$ nonempty, closed and convex, $f:H\to\mathbb R$ convex and lower semicontinuous with bounded sublevel sets $\{x\in C\mid f(x)\le a\}$), for every $x^n\in C$ the regularized problem
--   $$
--   \min\,\{\,f(x)+\|x-x^n\|^2 \mid x\in C\,\}
--   $$
--   has exactly one solution $x^{n+1}\in C$.
--
--   This is the claim built into the definition (13) of the algorithm ("$x^{n+1}\in C$ solution unique de …"): it guarantees that the sequence $(x^n)$ of §4.2 is well defined.
--
--   **Formalization Note** The paper applies (13) to $x^n\in C$, and the statement quantifies over exactly those $x^n$. The weight on the squared distance is $1$, as printed.
-- source:
--   Martinet, Régularisation d'inéquations variationnelles par approximations successives, R.I.R.O. 4(R-3) (1970), p. 157, §4.2, (13)

import Mathlib
import Definitions.Def_MartinetReg_ConvexMin_Setting

namespace MartinetReg.ConvexMin

/-- §4.2, (13), p. 157: for xⁿ ∈ C, the regularized problem min (f(x) + ‖x − xⁿ‖² | x ∈ C) has
exactly one solution xⁿ⁺¹ ∈ C. -/
theorem step_existsUnique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C) :
    ∀ xn ∈ C, ∃! y : H, IsProxStep f C xn y := by sorry

end MartinetReg.ConvexMin
