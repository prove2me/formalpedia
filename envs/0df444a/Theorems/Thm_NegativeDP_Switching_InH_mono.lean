-- Prove2me | Theorems.Thm_NegativeDP_Switching_InH_mono
-- name    : NegativeDP.Switching.InH_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:28.669991+00:00
-- url     : https://prove2.me/theorems/7fc531dd-31a9-4f24-b06f-1f90145a1cb5
-- title:
--   Proof of Theorem 9.3 — $I_{n-1}(\pi, w_n) \le I_n(\pi, w_{n+1})$
-- statement:
--   Consider a negative dynamic programming problem ($r\le0$, $\beta=1$) on non-empty Borel spaces. Let $\sigma,\tau$ be policies with continuation returns $u_n,v_n$, let $w_n=\max(u_n,v_n)$, and let $\pi$ be the switching policy of Theorem 9.3. Then for every $n\ge1$ and every initial state $s$,
--   $$I_{n-1}(\pi,w_n)(s)\le I_n(\pi,w_{n+1})(s),$$
--   where $I_n(\pi,w)$ is the expected return of following $\pi$ for $n$ stages and then receiving the history-dependent terminal reward $w(s_1,a_1,\dots,s_{n+1})$.
--
--   In words, following $\pi$ for one more stage before switching to the better of $\sigma$ and $\tau$ does not decrease the expected return.
--
--   **Formalization Note** Lean's index $n$ is the paper's $n-1$: the statement reads `InH P π n (wmax P σ τ n) s ≤ InH P π (n + 1) (wmax P σ τ (n + 1)) s` for all $n\ge0$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 888, proof of Theorem 9.3

import Mathlib
import Definitions.Def_NegativeDP_Switching_Model
open MeasureTheory ProbabilityTheory
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

namespace NegativeDP.Switching

/-- Proof of Theorem 9.3 (p. 888): `I_{n−1}(π, w_n) ≤ I_n(π, w_{n+1})`; Lean `n` is the paper's
`n − 1`. -/
theorem InH_mono {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) (hπ : IsSwitch P σ τ π)
    (n : ℕ) (s : S) :
    InH P π n (wmax P σ τ n) s ≤ InH P π (n + 1) (wmax P σ τ (n + 1)) s := by sorry
end NegativeDP.Switching
