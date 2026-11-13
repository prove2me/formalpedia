-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_probabilistic
-- name    : KSATSingleFlip.Connect.repair_probabilistic
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:36:16.971546+00:00
-- url     : https://prove2.me/theorems/3f3e7935-90d4-4794-aed5-7c483bd115b9
-- title:
--   High-probability success of Repair
-- statement:
--   For all sufficiently large $k$, all sufficiently large $n$, and any Poisson mean $m$ at most $(2^kn/k)\,\Lambda(k)$, fix an assignment $z$, a Glauber time $t$, and a degree cutoff $D$. Draw the clause count from $\operatorname{Pois}(m)$, draw the random $k$-CNF $\Phi^+$, and let $X$ be the $t$-step Glauber state on the subformula $\Phi_0$ of clauses satisfied by $z$. With probability at least $1-\exp(-\rho^8 n)$, the following implication holds: if $\Phi^+$ is regular and at most $\rho^4n$ omitted clauses have at most one true literal under $X$, then for every $W$ with $|W|\le\rho^2 n/2$, Repair has a completed run and every completed run returns a good $(X,W)$-repair.
--
--   $$\Pr[\text{the stated implication holds for all }W]\ge1-e^{-\rho^8 n}.$$
--
--   Here $\Lambda(k)$, $\rho(k)$, regularity, and good repair are the quantities defined in the paper. This is the probabilistic branch of Lemma 7.4, separate from deterministic correctness and cost.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://arxiv.org/abs/2611.05981, probabilistic branch of Lemma 7.4, printed p. 54 and proof pp. 60–64.

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_Glauber
import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

theorem repair_probabilistic :
    (∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ (z : Fin n → Bool) (t D : ℕ),
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              let Φp := ofList l
              let I0 := satIdx Φp z
              let X := glauberState (subF Φp I0) z s
              Reg k D Φp → ((omittedWeak Φp I0 X).card : ℝ) ≤ rho k ^ 4 * n →
                ∀ W : Finset (Fin n), (W.card : ℝ) ≤ rho k ^ 2 * n / 2 →
                  (∃ r i, RepairRun k Φp I0 X (RState.init Φp X W) r i) ∧
                  ∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
                    RepairRun k Φp I0 X (RState.init Φp X W) r i →
                      ∃ U y, r = some (U, y) ∧ IsGoodRepair k Φp X W U y)) := by sorry

end KSATSingleFlip.Connect
