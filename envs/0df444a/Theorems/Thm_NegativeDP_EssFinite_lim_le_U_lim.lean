-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_lim_le_U_lim
-- name    : NegativeDP.EssFinite.lim_le_U_lim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:58.39725+00:00
-- url     : https://prove2.me/theorems/b5e8674a-9f54-4091-9106-4f31912f7c74
-- title:
--   Proof of Theorem 9.1, p. 887 — the limit of value iteration is conserved by U
-- statement:
--   In Strauch's negative dynamic programming problem (non-empty Borel $S$, $A$, law of motion $q$, Borel return $r\le0$ with $qr>-\infty$), suppose that $A$ is essentially finite by the Markov policy $\pi^*=(f_1,f_2,\dots)$, and let $U$ be the operator associated with $\pi^*$. Let
--   $$v^\infty(s)=\lim_{n\to\infty}U^n0(s)=\inf_n U^n0(s)$$
--   (the sequence is non-increasing). Then
--   $$Uv^\infty(s)\ge v^\infty(s)\qquad\text{for every } s\in S.$$
--
--   In the paper this limit is called $v^*$ inside the proof of Theorem 9.1. Together with the bound $I(\pi)\le v^\infty$ it is one of the two steps of the proof of Theorem 9.1.
--
--   **Formalization Note** $v^\infty$ is written as the pointwise infimum of $U^n0$ in `EReal`; it is non-positive, so $U$ is applied to an element of $M(S)$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 887, proof of Theorem 9.1 (second paragraph)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model

open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Proof of Theorem 9.1 (N), Strauch (1966), p. 887, second paragraph. If `A` is essentially
finite by `π*` and `U` is its operator, the limit `v^∞ = lim_n NegativeDP.OptEq.U^n 0 = inf_n NegativeDP.OptEq.U^n 0` (the
paper's "v*" inside this proof) satisfies `U v^∞ ≧ v^∞`. -/
theorem lim_le_U_lim (P : NegativeDP.Stationary.Problem S A) (πstar : MarkovPlan S A)
    (h : EssentiallyFinite P πstar) :
    ∀ s, (⨅ n, (NegativeDP.OptEq.U P πstar)^[n] 0 s) ≤ NegativeDP.OptEq.U P πstar (fun t => ⨅ n, (NegativeDP.OptEq.U P πstar)^[n] 0 t) s := by sorry

end NegativeDP.EssFinite
