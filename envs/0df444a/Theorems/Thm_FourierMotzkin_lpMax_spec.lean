-- Prove2me | Theorems.Thm_FourierMotzkin_lpMax_spec
-- name    : FourierMotzkin.lpMax_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:43:25.247359+00:00
-- url     : https://prove2.me/theorems/783042d9-68c4-40ea-976b-814c6c4ecfbb
-- title:
--   Correctness of the Fourier–Motzkin LP solver
-- statement:
--   For a finite system $\mathrm{sys}$ of linear inequalities over the reals and an objective vector $c$, the Fourier–Motzkin solver $\mathrm{lpMax}(c,\mathrm{sys})$ satisfies:
--
--   1. it returns `infeasible` if and only if the system has no solution;
--   2. it returns `unbounded` if and only if the system has a solution and $\{c\cdot x : x\ \text{feasible}\}$ is not bounded above;
--   3. whenever it returns `opt v`, the point $x^*=\mathrm{argmax}(c,\mathrm{sys})$ is feasible with $c\cdot x^*=v$, and $c\cdot x\le v$ for every feasible $x$.
--
--   In particular every feasible bounded linear program is solved exactly, with an optimal solution, using only field operations and comparisons; this is what an untimed implementation of the sublinear TSP estimator needs for its local linear programs.
-- source:
--   A. Schrijver, Theory of Linear and Integer Programming (1986), §12.2 (Fourier–Motzkin elimination); used for the local LPs in Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, §9.4 p.42.

import Mathlib
import Definitions.Def_FourierMotzkin_basic

namespace FourierMotzkin

/-- **Correctness of the exact LP solver `lpMax`.** The solver reports infeasibility exactly when the system has no
solution, unboundedness exactly when it is feasible with objective unbounded above, and otherwise returns the optimum
`v` together with an optimal point `argmax c sys`. -/
theorem lpMax_spec (c : List ℝ) (sys : System) :
    (lpMax c sys = .infeasible ↔ ¬ ∃ x, Sat sys x) ∧
    (lpMax c sys = .unbounded ↔ (∃ x, Sat sys x) ∧ ¬ BddAbove (objValues c sys)) ∧
    (∀ v, lpMax c sys = .opt v →
      Sat sys (argmax c sys) ∧ dot c (argmax c sys) = v ∧ ∀ x, Sat sys x → dot c x ≤ v) := by sorry

end FourierMotzkin
