-- Prove2me | Theorems.Thm_GoldfarbIdnani_DualQP_step2_round
-- name    : GoldfarbIdnani.DualQP.step2_round
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:27:28.799218+00:00
-- url     : https://prove2.me/theorems/ed80e956-2ec7-4c79-ba09-a216cc4ea28d
-- title:
--   Section 3, p. 11 — a round of Step 2 from an S-pair ends in a new S-pair with larger $f$ or detects infeasibility
-- statement:
--   Let $G$ be symmetric positive definite, let $(x, A)$ be an S-pair for (1.1), and let $p \in K \setminus A$ be violated, $s_p(x) < 0$. Start the dual algorithm in Step 2(a) with point $x$, active set $A$, violated constraint $p$ and dual vector $u^+ = (u(x); 0)$, and run it, through any of its admissible choices, as long as it is in Step 2. The initial active set has $q = |A| \le \min(m,n)$. No run has $q+2$ Step-2 transitions, so at most $q$ partial or dual steps precede one full step or an infeasibility STOP. Every reachable Step-2 state has a successor. Every state reached in this way satisfies:
--
--   1. if it is the infeasibility STOP, the QPP (1.1) has no feasible point;
--   2. if it is Step 1 with point $\bar x$, active set $A'$ and stored multipliers $u'$, then $A' = \bar A \cup \{p\}$ for some $\bar A \subseteq A$, $(\bar x, A')$ is an S-pair,
--
--   $$
--   f(\bar x) > f(x),
--   $$
--
--   and $u' = u(\bar x) = N'^*g(\bar x)$ is the multiplier vector of the new active set.
--
--   This is the paper's summary of Step 2 before Theorem 3: a sequence of partial or dual steps (each dropping one constraint of $A$, hence at most $|A|$ of them) and one full step produces a new S-pair with a strictly larger objective value, so no S-pair recurs, unless infeasibility is detected by Theorems 1 and 2.
--
--   **Formalization Note.** The run is restricted to transitions out of Step-2 states, so it stops at the first return to Step 1. The length bound is stated as the impossibility of $q+2$ Step-2 transitions, and progress is stated for each reachable Step-2 state. The statement about the stored multipliers records that the algorithm's updated vector $u \leftarrow u^+$ is the multiplier vector $N^*g$ at the new point, which is what Step 1 assumes when it next sets $u^+ \leftarrow (u;0)$.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), p. 11, Section 3 (paragraph before Theorem 3); p. 4, Basic approach, Step 1(c)

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_Algorithm

namespace GoldfarbIdnani.DualQP

open Matrix

theorem step2_round {n m : ℕ} (a : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m)
    (hG : G.PosDef) (hS : IsSPair a G C b x A) (hpA : p ∉ A) (hp : slack C b x p < 0) :
    let start := State.step2 x A p (restrict A (multVec G C A (grad a G x)))
    let roundStep : State n m → State n m → Prop :=
      fun s s' => Step a G C b s s' ∧ ∃ x' A' p' u', s = State.step2 x' A' p' u'
    A.card ≤ min m n ∧
    (¬ ∃ σ : ℕ → State n m, σ 0 = start ∧
      ∀ k < A.card + 2, roundStep (σ k) (σ (k + 1))) ∧
    (∀ s : State n m, Relation.ReflTransGen roundStep start s →
      (∃ x' A' p' u', s = State.step2 x' A' p' u') →
      ∃ s', roundStep s s') ∧
    (∀ s : State n m,
      Relation.ReflTransGen
        roundStep start s →
      (s = State.stopInfeasible → ∀ y, ¬ Feasible C b y) ∧
      (∀ xbar A' u', s = State.step1 xbar A' u' →
        (∃ Abar ⊆ A, A' = insert p Abar) ∧
        IsSPair a G C b xbar A' ∧
        f a G x < f a G xbar ∧
        u' = multVec G C A' (grad a G xbar))) := by sorry

end GoldfarbIdnani.DualQP
