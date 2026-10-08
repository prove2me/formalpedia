-- Prove2me | Theorems.Thm_MartinetReg_VI_minty
-- name    : MartinetReg.VI.minty
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:46.708422+00:00
-- url     : https://prove2.me/theorems/9e8cbd62-33ec-49e1-b4af-a64ced5c2a18
-- title:
--   §2.3, (5) — Minty's characterization: M = {x̄ ∈ C | (Tx, x − x̄) ≥ 0 ∀ x ∈ C}
-- statement:
--   Let $H$ be a real Hilbert space, $C\subseteq H$ convex, closed and bounded, and $T:H\to H'$ monotone and hemicontinuous on $C$. Let $M$ be the solution set of the variational inequality (1). Then
--   $$
--   M=\{\bar x\in C \mid (Tx,\, x-\bar x)\ge 0\ \ \forall x\in C\}.
--   $$
--   In words: $\bar x\in C$ solves $(T\bar x, x-\bar x)\ge0$ for all $x\in C$ if and only if $(Tx, x-\bar x)\ge0$ for all $x\in C$, where now the operator is evaluated at the variable point $x$.
--
--   The right-hand side is an intersection of weakly closed half-spaces with $C$; this is what lets the weak limit pass in the proof of Théorème 1.
--
--   **Formalization Note.** The paper derives (5) "des propriétés de monotonie et d'hémicontinuité" (citing [1]); we state it under the full standing hypotheses of §2.1 (`Standing T C`), which is the context of the paper. The free point of $C$ is named $y$ in Lean.
-- source:
--   Martinet, Régularisation d'inéquations variationnelles par approximations successives, R.I.R.O. 4(R-3) (1970), p. 155, §2.3, (5)

import Mathlib
import Definitions.Def_MartinetReg_VI_Setting

namespace MartinetReg.VI

open Filter Topology

/-- §2.3, (5), p. 155: Minty's characterization of the solution set `M` of (1). -/
theorem minty {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C) :
    solSet T C = {xbar | xbar ∈ C ∧ ∀ y ∈ C, 0 ≤ T y (y - xbar)} := by sorry

end MartinetReg.VI
