-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_return_le_lim
-- name    : NegativeDP.EssFinite.return_le_lim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:37.304282+00:00
-- url     : https://prove2.me/theorems/27cfc6b9-c585-4842-ae66-daba9d139cb5
-- title:
--   Proof of Theorem 9.1, p. 887 — under essential finiteness every policy's return is at most lim U^n0
-- statement:
--   In Strauch's negative dynamic programming problem (non-empty Borel $S$, $A$, law of motion $q$, Borel return $r\le0$ with $qr>-\infty$), suppose that $A$ is essentially finite by the Markov policy $\pi^*=(f_1,f_2,\dots)$, and let $U$ be the operator associated with $\pi^*$. Put $v_n=U^n0$. Then:
--
--   1. $v_n(s)\ge v_{n+1}(s)$ for every $n$ and every state $s$, so $v^\infty=\lim_n v_n=\inf_n v_n$ exists;
--   2. every policy $\pi$ satisfies, at every state $s$,
--   $$I(\pi)(s)\le v^\infty(s)=\inf_{n}\,U^n0(s).$$
--
--   In the paper this limit is called $v^*$ inside the proof of Theorem 9.1; it is a different object from $v^*=\sup_\pi I(\pi)$ until the theorem identifies the two. This inequality is one half of Theorem 9.1 (a).
--
--   **Formalization Note** Monotonicity is stated as `Antitone` in $n$ for each state, and the limit of the non-increasing sequence is written as its infimum in `EReal`. The policy $\pi$ ranges over every randomized history-dependent plan.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 887, proof of Theorem 9.1 (first paragraph)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model

open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Proof of Theorem 9.1 (N), Strauch (1966), p. 887, first paragraph. If `A` is essentially
finite by `π*` and `U` is its operator, then `v_n = NegativeDP.OptEq.U^n 0` is non-increasing in `n`, and
every policy satisfies `I(π) ≦ lim_n v_n = inf_n v_n`. -/
theorem return_le_lim (P : NegativeDP.Stationary.Problem S A) (πstar : MarkovPlan S A)
    (h : EssentiallyFinite P πstar) :
    (∀ s, Antitone (fun n => (NegativeDP.OptEq.U P πstar)^[n] 0 s)) ∧
      ∀ (σ : Plan (S := S) (A := A)) (s : S), NegativeDP.Stationary.I P σ s ≤ ⨅ n, (NegativeDP.OptEq.U P πstar)^[n] 0 s := by sorry

end NegativeDP.EssFinite
