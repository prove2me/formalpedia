-- Prove2me | Theorems.Thm_GoldfarbIdnani_DualQP_theorem_3_dual_algorithm_terminates
-- name    : GoldfarbIdnani.DualQP.theorem_3_dual_algorithm_terminates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:27:34.26597+00:00
-- url     : https://prove2.me/theorems/1bca6ac4-ebd9-4f6f-bede-d1ce6741f64b
-- title:
--   Theorem 3 — the dual algorithm solves the QP (1.1) or detects its infeasibility in finitely many steps
-- statement:
--   Let $a \in \mathbb R^n$, let $G$ be an $n \times n$ symmetric positive definite matrix, let $C$ be an $n \times m$ matrix with columns $n_1, \dots, n_m$ and let $b \in \mathbb R^m$. Consider the strictly convex quadratic program
--
--   $$
--   \text{minimize } f(x) = a^{\mathsf T}x + \tfrac12x^{\mathsf T}Gx \quad\text{subject to}\quad C^{\mathsf T}x - b \ge 0,
--   $$
--
--   and the dual algorithm of Goldfarb and Idnani started from Step 0 (the unconstrained minimizer $x^0 = -G^{-1}a$ with empty active set), with the violated constraint in Step 1 and the dropped constraint in Step 2 chosen arbitrarily among the admissible ones. Then:
--
--   1. **finite termination**: there is no infinite run of the algorithm, whatever choices are made;
--   2. **correctness**: every state reachable from Step 0 at which the algorithm cannot continue is either a STOP at a point $x$ that is an optimal solution of the QP (feasible, and $f(x) \le f(y)$ for every feasible $y$), or the infeasibility STOP, and then the QP has no feasible point.
--
--   This is the main theorem of the paper's Section 3: the dual active-set method, which maintains optimality for a sequence of subproblems and increases $f$ at every new S-pair, needs no phase 1 and always ends with a correct answer.
--
--   **Formalization Note.** The paper says the algorithm "will solve the QPP (1.1) or indicate that it has no feasible solution in a finite number of steps". The Lean statement makes this explicit for the nondeterministic step relation `Step` of the module `GoldfarbIdnani.DualQP.Algorithm`: (1) there is no sequence of states $\sigma_0, \sigma_1, \dots$ with $\sigma_0$ the Step-0 state and a step from each $\sigma_k$ to $\sigma_{k+1}$; (2) every state reachable from Step 0 with no outgoing step is a correct STOP, which also rules out a run that gets stuck elsewhere. Both parts quantify over every run, so they hold for every rule of choosing $p$ and $k$.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), p. 11, Theorem 3

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_Algorithm

namespace GoldfarbIdnani.DualQP

open Matrix

theorem theorem_3_dual_algorithm_terminates {n m : ℕ} (a : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (hG : G.PosDef) :
    (¬ ∃ σ : ℕ → State n m, σ 0 = initState a G ∧ ∀ k, Step a G C b (σ k) (σ (k + 1))) ∧
    (∀ s : State n m, Relation.ReflTransGen (Step a G C b) (initState a G) s →
      (∀ s', ¬ Step a G C b s s') →
      (∃ x, s = State.stopOptimal x ∧ IsOptimal a G C b x) ∨
        (s = State.stopInfeasible ∧ ∀ y, ¬ Feasible C b y)) := by sorry

end GoldfarbIdnani.DualQP
