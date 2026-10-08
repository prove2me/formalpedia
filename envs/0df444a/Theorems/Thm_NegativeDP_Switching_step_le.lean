-- Prove2me | Theorems.Thm_NegativeDP_Switching_step_le
-- name    : NegativeDP.Switching.step_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:18.829988+00:00
-- url     : https://prove2.me/theorems/51da7647-178e-4c57-a65d-56368484c5a5
-- title:
--   Proof of Theorem 9.3 — $w_n \le \pi_n(r + w_{n+1})$ on $B_n$ and on $B_n^c$
-- statement:
--   Consider a negative dynamic programming problem ($r\le0$, $\beta=1$) on non-empty Borel spaces. Let $\sigma,\tau$ be policies with continuation returns $u_n,v_n$, let $w_n=\max(u_n,v_n)$, and let $\pi$ be the switching policy of Theorem 9.3 ($\pi_n=\sigma_n$ where $u_n>v_n$, $\pi_n=\tau_n$ elsewhere). Then at every stage $n$ and every history $h=(s_1,a_1,\dots,s_n)$,
--   $$w_n(h)\le\pi_n(r+w_{n+1})(h),$$
--   where $\pi_n(r+w_{n+1})(h)$ is the expectation of $r(s_n,a,t)+w_{n+1}(h,a,t)$ when $a\sim\pi_n(\cdot\mid h)$ and $t\sim q(\cdot\mid s_n,a)$.
--
--   This is the one-step improvement inequality of the proof of Theorem 9.3: switching for one stage to the better of $\sigma$ and $\tau$ and continuing with the better of them afterwards does at least as well as committing to the better one now.
--
--   **Formalization Note** The paper's stage $n$ is Lean's index $n-1$; $\beta=1$. The paper states the inequality separately on $B_n$ and $B_n^c$; together they cover every history.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 888, proof of Theorem 9.3 (displayed inequalities)

import Mathlib
import Definitions.Def_NegativeDP_Switching_Model
open MeasureTheory ProbabilityTheory
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

namespace NegativeDP.Switching

/-- Proof of Theorem 9.3 (p. 888): `w_n ≤ π_n(r + w_{n+1})` on `B_n` and on `B_nᶜ`, at every
history. Lean decision `n` is the paper's stage `n + 1`. -/
theorem step_le {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) (hπ : IsSwitch P σ τ π)
    (n : ℕ) (h : Hist S A n) :
    wmax P σ τ n h ≤ stepOp P π n (wmax P σ τ (n + 1)) h := by sorry
end NegativeDP.Switching
