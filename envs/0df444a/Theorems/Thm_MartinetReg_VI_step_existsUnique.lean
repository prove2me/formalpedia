-- Prove2me | Theorems.Thm_MartinetReg_VI_step_existsUnique
-- name    : MartinetReg.VI.step_existsUnique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:35.630395+00:00
-- url     : https://prove2.me/theorems/2321c4ef-7dfa-493e-bfc1-a494a0eceaa1
-- title:
--   §2.2 — the regularization step (2) has exactly one solution xⁿ⁺¹ ∈ C
-- statement:
--   Let $H$ be a real Hilbert space, $C\subseteq H$ convex, closed and bounded, and $T:H\to H'$ monotone and hemicontinuous on $C$. For every $x^n\in C$ there is exactly one $y\in C$ such that
--   $$
--   (Ty,\, x-y)+\langle y-x^n,\, x-y\rangle\ge 0\qquad\forall x\in C .
--   $$
--
--   This is the claim of §2.2 ("on détermine $x^{n+1}\in C$ *unique* tel que (2)") that makes the regularization algorithm well defined: starting from any $x^0\in C$ it produces a unique sequence.
--
--   **Formalization Note.** Existence and uniqueness are stated together as `∃!`. The standing hypotheses of §2.1 are bundled in `Standing T C`; $H'$ is `StrongDual ℝ H`, $(\varphi,y)$ is `φ y`, and $\langle a,b\rangle$ is `inner ℝ a b`.
-- source:
--   Martinet, Régularisation d'inéquations variationnelles par approximations successives, R.I.R.O. 4(R-3) (1970), p. 155, §2.2, (2)

import Mathlib
import Definitions.Def_MartinetReg_VI_Setting

namespace MartinetReg.VI

open Filter Topology

/-- §2.2, p. 155: for every `xn ∈ C` there is exactly one `y ∈ C` satisfying (2). -/
theorem step_existsUnique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C) :
    ∀ xn ∈ C, ∃! y : H, IsRegStep T C xn y := by sorry

end MartinetReg.VI
