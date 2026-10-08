-- Prove2me | Theorems.Thm_NegativeDP_Switching_step_eq
-- name    : NegativeDP.Switching.step_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:17.436262+00:00
-- url     : https://prove2.me/theorems/d080e545-4e42-4abe-9339-f176b089fdf1
-- title:
--   Proof of Theorem 9.3 — $w_n = \pi_n(r + u_{n+1})$ on $B_n$ and $w_n = \pi_n(r + v_{n+1})$ on $B_n^c$
-- statement:
--   Consider a negative dynamic programming problem ($r\le0$, $\beta=1$) on non-empty Borel spaces. Let $\sigma,\tau$ be policies with continuation returns $u_n,v_n$, let $w_n=\max(u_n,v_n)$, and let $\pi$ be the switching policy: $\pi_n=\sigma_n$ on $B_n=\{u_n>v_n\}$ and $\pi_n=\tau_n$ on $B_n^c$. Then at every stage $n$ and every history $h=(s_1,a_1,\dots,s_n)$,
--   $$w_n(h)=\begin{cases}\pi_n(r+u_{n+1})(h)&\text{if }h\in B_n,\\ \pi_n(r+v_{n+1})(h)&\text{if }h\in B_n^c,\end{cases}$$
--   where $\pi_n(r+x)(h)$ is the expectation of $r(s_n,a,t)+x(h,a,t)$ when $a\sim\pi_n(\cdot\mid h)$ and $t\sim q(\cdot\mid s_n,a)$.
--
--   These are the equalities in the first halves of the displayed inequalities in the proof of Theorem 9.3; they combine the choice of $\pi$ with the one-step recursion of the continuation returns.
--
--   **Formalization Note** The paper's stage $n$ is Lean's index $n-1$. The paper's $\beta=1$ in the negative case. "$\pi$ is the switching policy" is the hypothesis `IsSwitch P σ τ π`.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 888, proof of Theorem 9.3 (displayed equalities)

import Mathlib
import Definitions.Def_NegativeDP_Switching_Model
open MeasureTheory ProbabilityTheory
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

namespace NegativeDP.Switching

/-- Proof of Theorem 9.3 (p. 888), first halves of the display: on `B_n` (σ's continuation
return strictly larger) `w_n = π_n(r + u_{n+1})`, and on `B_nᶜ` `w_n = π_n(r + v_{n+1})`. Lean decision
`n` is the paper's stage `n + 1`. -/
theorem step_eq {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) (hπ : IsSwitch P σ τ π)
    (n : ℕ) (h : Hist S A n) :
    (contReturn P τ n h < contReturn P σ n h →
      wmax P σ τ n h = stepOp P π n (contReturn P σ (n + 1)) h) ∧
    (¬ contReturn P τ n h < contReturn P σ n h →
      wmax P σ τ n h = stepOp P π n (contReturn P τ (n + 1)) h) := by sorry
end NegativeDP.Switching
