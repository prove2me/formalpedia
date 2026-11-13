-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_deterministic
-- name    : KSATSingleFlip.Connect.repair_deterministic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:35:51.219205+00:00
-- url     : https://prove2.me/theorems/e74581c5-a187-4681-9e41-490784f841cf
-- title:
--   Deterministic correctness and cost of Repair
-- statement:
--   For every $k\ge1$ there is a constant $C_k>0$ with the following property. Let $\Phi^+$ be a finite proper $k$-CNF with $n$ variables and $m$ clauses, let $\Phi_0\subseteq\Phi^+$, let $x$ satisfy $\Phi_0$, and let $W$ be a set of variables. Algorithm 3 has a completed run. Every completed run either returns failure or returns an $(x,W)$-repair $(U,y)$, and every completed or partial run has declared cost at most
--
--   $$C_k n(n+m).$$
--
--   A repair satisfies $W\subseteq U$, $y\models\Phi^+$, and $y=x$ outside $U$. Moreover, for every subformula $\Psi\subseteq\Phi^+$, every solution $\sigma$ of $\Psi$ that agrees with $x$ outside $U$ is connected to $y$ within the solutions of $\Psi$ by a path of exactly $d_H(\sigma,y)$ single-variable flips. The statement covers every allowed choice in the nondeterministic formalization; the separate high-probability good-repair guarantee is not included.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://arxiv.org/abs/2611.05981, Algorithm 3 and deterministic branch of Lemma 7.4, printed pp. 60–62.

import Definitions.Def_KSATSingleFlip_Connect_Repair
import Definitions.Def_SATComputability

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

theorem repair_deterministic :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (Φp : List (ProperClause n k))
      (I0 : Finset (Fin (ofList Φp).length)) (x : Fin n → Bool) (W : Finset (Fin n)),
      x ∈ sols (subF (ofList Φp) I0) →
        (∃ r i, RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i) ∧
        (∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
          RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i →
            (r = none ∨ ∃ U y, r = some (U, y) ∧ IsRepair (ofList Φp) x W U y) ∧
            (repairCost n Φp.length i : ℝ) ≤ C * n * (n + Φp.length)) ∧
        (∀ (s : RState (ofList Φp) x) (j : ℕ),
          RepairReach k (ofList Φp) I0 x (RState.init (ofList Φp) x W) s j →
            (repairCost n Φp.length j : ℝ) ≤ C * n * (n + Φp.length)) := by sorry

end KSATSingleFlip.Connect
