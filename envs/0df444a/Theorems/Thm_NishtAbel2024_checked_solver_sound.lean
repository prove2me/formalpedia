-- Prove2me | Theorems.Thm_NishtAbel2024_checked_solver_sound
-- name    : NishtAbel2024.checked_solver_sound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T03:15:27.750972+00:00
-- url     : https://prove2.me/theorems/94ac8d9d-8707-4e7f-90d3-532126641bd0
-- title:
--   Soundness of a fuel-bounded checked constraint solver
-- statement:
--   Let $\Psi$ be a size context, $C$ a finite list of size constraints, $T$ a finite list of tracked variables, and $n\in\mathbb N$ a fuel bound. Write $S_n(\Psi,C,T)$ for the checked wrapper around the existing constraint solver. For every flexible substitution $\varphi$,
--
--   $$
--   S_n(\Psi,C,T)=\operatorname{some}(\varphi)
--   \quad\Longrightarrow\quad
--   \operatorname{Coherent}(\Psi,C,\varphi).
--   $$
--
--   Coherence means that the substitution fixes every rigid variable, maps every variable to a well-formed size expression in $\Psi$, and satisfies every constraint using the current formalization's normalization of right-hand bounds. This gives a sound acceptance criterion for the candidate computed by the existing solver.
--
--   The wrapper is incomplete: returning no candidate can reflect insufficient fuel or an incomplete comparison search and does not imply unsatisfiability. The theorem does not certify separate raw function-call bounds, establish completeness or correctness of the original Algorithm 1, or prove termination of a program.
--
--   **Formalization Note.** This is an auxiliary construction for the current Lean model, not the thesis's full Theorem 14.
-- source:
--   Auxiliary certificate for the existing Lean solver, inspired by K. Nisht, Type-Based Termination Checking in Agda (2024), §6.4, pp. 56–58, https://knisht.github.io/agda/msc.pdf. The checked wrapper and this conditional result are not the thesis’s full Theorem 14 or its original algorithm.

import Definitions.Def_NishtAbel2024_CheckedConstraintSolver

namespace NishtAbel2024

theorem checked_solver_sound :
    ∀ (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) (φ : FlexSubst),
      CheckedConstraintSolver.checkedSolve fuel Ψ C T = some φ → CoherentSubst Ψ C φ := by
  sorry

end NishtAbel2024
