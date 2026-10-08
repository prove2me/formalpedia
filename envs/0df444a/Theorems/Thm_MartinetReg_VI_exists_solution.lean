-- Prove2me | Theorems.Thm_MartinetReg_VI_exists_solution
-- name    : MartinetReg.VI.exists_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:24.723442+00:00
-- url     : https://prove2.me/theorems/8fca93c5-5875-4645-8c3d-6afc91d7bf37
-- title:
--   §2.1 — the monotone variational inequality (1) on a bounded closed convex set has a solution
-- statement:
--   Let $H$ be a real Hilbert space, $C\subseteq H$ a nonempty, convex, closed and bounded set, and $T:H\to H'$ monotone and hemicontinuous on $C$. Then the variational inequality (1) has at least one solution: there exists $\bar x\in C$ with
--   $$
--   (T\bar x,\, x-\bar x)\ge 0\qquad\forall x\in C ,
--   $$
--   i.e. the solution set $M$ is nonempty.
--
--   The paper cites this (Lions–Stampacchia, [1]) right after stating (1); the proof of Lemme 1 relies on it when it picks an arbitrary $\bar x\in M$.
--
--   **Formalization Note.** The paper states "(1) a, au moins, une solution" under the hypotheses of §2.1; we state it with the additional hypothesis that $C$ is nonempty, which is implicit in the paper (the claim is false for $C=\emptyset$). $H'$ is `StrongDual ℝ H` and $(\varphi,y)$ is `φ y`; the standing hypotheses are bundled in `Standing T C`.
-- source:
--   Martinet, Régularisation d'inéquations variationnelles par approximations successives, R.I.R.O. 4(R-3) (1970), p. 155, §2.1, after (1) (citing Lions–Stampacchia, C.P.A.M. XX (1967) 493–519)

import Mathlib
import Definitions.Def_MartinetReg_VI_Setting

namespace MartinetReg.VI

open Filter Topology

/-- §2.1, after (1), p. 155: the variational inequality (1) has at least one solution
(C nonempty is implicit in the paper). -/
theorem exists_solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C) (hne : C.Nonempty) :
    (solSet T C).Nonempty := by sorry

end MartinetReg.VI
