-- Prove2me | Theorems.Thm_NegativeDP_Switching_InH_ge
-- name    : NegativeDP.Switching.InH_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:18.501997+00:00
-- url     : https://prove2.me/theorems/62f8ef33-ecc4-40d2-abb7-10f33ed9395e
-- title:
--   Proof of Theorem 9.3 — $I_{n-1}(\pi, w_n) \ge \max(I(\sigma), I(\tau))$ for all $n$
-- statement:
--   Consider a negative dynamic programming problem ($r\le0$, $\beta=1$) on non-empty Borel spaces. Let $\sigma,\tau$ be policies with continuation returns $u_n,v_n$, let $w_n=\max(u_n,v_n)$, and let $\pi$ be the switching policy of Theorem 9.3. Then for every $n\ge1$ and every initial state $s$,
--   $$I_{n-1}(\pi,w_n)(s)\ge\max\big(I(\sigma)(s),I(\tau)(s)\big).$$
--   The left side is the expected return of following $\pi$ for $n-1$ stages and then switching to the better of $\sigma$ and $\tau$.
--
--   This bound, uniform in $n$, is what the proof of Theorem 9.3 passes to the limit.
--
--   **Formalization Note** Lean's index $n$ is the paper's $n-1$, so the statement is for all $n\ge0$. The printed text and the Lean statement both use $I(\tau)$ as the second argument.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 888, proof of Theorem 9.3

import Mathlib
import Definitions.Def_NegativeDP_Switching_Model
open MeasureTheory ProbabilityTheory
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

namespace NegativeDP.Switching

/-- Proof of Theorem 9.3 (p. 888): `I_{n−1}(π, w_n) ≥ max(I(σ), I(τ))` for all `n`; Lean `n` is
the paper's `n − 1`. -/
theorem InH_ge {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) (hπ : IsSwitch P σ τ π)
    (n : ℕ) (s : S) :
    max (I P σ s) (I P τ s) ≤ InH P π n (wmax P σ τ n) s := by sorry
end NegativeDP.Switching
