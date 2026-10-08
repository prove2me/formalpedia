-- Prove2me | Theorems.Thm_NegativeDP_Switching_InH_zero
-- name    : NegativeDP.Switching.InH_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:05.920685+00:00
-- url     : https://prove2.me/theorems/c1f3a597-799e-4125-9efe-eae8c943799c
-- title:
--   Proof of Theorem 9.3 — $I_0(\pi, w_1) = w_1 = \max(I(\sigma), I(\tau))$
-- statement:
--   Consider a negative dynamic programming problem (non-positive returns, $\beta=1$) on non-empty Borel state and action spaces. Let $\sigma$ and $\tau$ be policies with continuation returns $u_n$ and $v_n$, and let $w_n=\max(u_n,v_n)$. Then for every policy $\pi$ and every initial state $s$,
--   $$I_0(\pi,w_1)(s)=w_1(s)=\max\big(I(\sigma)(s),I(\tau)(s)\big).$$
--   Here $I_0(\pi,w_1)$ is the expected return when the process is stopped before the first stage and the terminal reward $w_1$ is received at the initial history $(s)$.
--
--   This is the starting point of the induction in the proof of Theorem 9.3: the continuation return of a policy from the empty history is its expected return.
--
--   **Formalization Note** The paper's $w_1$ is `wmax P σ τ 0` evaluated at the initial history `Hist.start s` (Lean's index $0$ is the paper's stage $1$). The return $I$ is defined through the law of the history from the initial state, the continuation return through the continuation law, so the second equality is a statement about those two constructions.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 888, proof of Theorem 9.3

import Mathlib
import Definitions.Def_NegativeDP_Switching_Model
open MeasureTheory ProbabilityTheory
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

namespace NegativeDP.Switching

/-- Proof of Theorem 9.3 (p. 888): `I_0(π, w_1) = w_1 = max(I(σ), I(τ))`, for every plan `π`. -/
theorem InH_zero {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) (s : S) :
    InH P π 0 (wmax P σ τ 0) s = wmax P σ τ 0 (Hist.start s) ∧
    wmax P σ τ 0 (Hist.start s) = max (I P σ s) (I P τ s) := by sorry
end NegativeDP.Switching
