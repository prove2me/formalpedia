-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_1_5
-- name    : MDPFinance.OptimalStopping.theorem_10_1_5
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:44:52.903639+00:00
-- url     : https://prove2.me/theorems/da059701-b72f-4f45-a2c6-4a5b8a335455
-- title:
--   Theorem 10.1.5 — the stationary stopping problem with finite horizon
-- statement:
--   **Theorem 10.1.5** (p. 308). Suppose a stationary stopping problem with finite horizon $N$
--   is given. Then it holds:
--
--   a) $J_0 = g$ and $J_n = \mathcal{T}J_{n-1}$ for $n = 1,\dots,N$ where
--      $\mathcal{T}v(x) = \max\{g(x),\ c(x) + \beta\int v(x')Q^X(dx'|x)\}$, $x \in E$.
--   b) $g \le J_n \le J_{n+1}$ for all $n \in \mathbb{N}_0$.
--   c) Define $d_n(x) := g(x) - c(x) - \beta\int J_{n-1}(x')Q^X(dx'|x)$ for $n = 1,\dots,N$. Then
--      $d_{n+1}(x) = d_1(x) - \beta\int d_n^-(x')Q^X(dx'|x)$.
--   d) Let $S_n^* := \{x \in E \mid J_n(x) = g(x)\}$ and $f_n^* := \mathbf 1_{S_n^*}$. Then
--      $S_0^* = E$, $S_n^* = \{x \in E \mid d_n(x) \ge 0\}$ and $S_{n+1}^* \subset S_n^*$. The policy
--      $(f_N^*,\dots,f_1^*)$ is optimal and
--      $\tau^* := \min\{n \in \{0,1,\dots,N\} \mid X_n \in S_{N-n}^*\}$ is an optimal stopping time.
--
--   b) is the monotonicity that makes §10.2's limit $J := \lim_n J_n$ exist at all, so it is not a
--   remark in passing. $S_{n+1}^* \subset S_n^*$ says, in the book's reading, that "the tendency to
--   stop is non-decreasing as time goes by".
--
--   $d_n^-$ is the negative part $\max(-d_n,0)$, which is what makes $J_n = g + d_n^-$ (Eq. (10.2),
--   p. 309) and $S_n^* = \{d_n \ge 0\}$ consistent.
--
--   As in Theorem 10.1.3, a) is stated as the identification of the value iteration with the *value* of
--   the $n$-stage stopping problem, not as the recursion alone, which would restate the definition of
--   $J$.
--
--   **Moderation note.** The book's finite-horizon standing assumption `(B_N)` was missing; added. a) identifies the value iteration with the `n`-stage value in `[-∞,∞]`; c) uses `d_n^- = max(−d_n, 0)` in `[-∞,∞]`; d) optimality is attainment of `J_N`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 308 (PDF 316), Theorem 10.1.5

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.1.5** (p. 308), under (B_N). a) `J_0 = g`, `J_n = T J_{n-1}` — the value iteration
computes the value `J_n(x) = sup_{τ ≤ n} 𝔼_x[R_τ]` of the `n`-stage problem. b) `g ≤ J_n ≤ J_{n+1}`.
c) `d_{n+1}(x) = d_1(x) − β ∫ d_n^-(x') Q^X(dx'|x)`. d) `S_0^* = E`, `S_n^* = {d_n ≥ 0}`,
`S_{n+1}^* ⊂ S_n^*`; the policy `(f_N^*,…,f_1^*)` is optimal and `τ^* := min{n ∈ {0,…,N} | X_n ∈
S_{N-n}^*}` is an optimal stopping time. -/
theorem theorem_10_1_5 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E) (N : ℕ)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) :
    (∀ n : ℕ, n ≤ N → ∀ x : E, P.J n x = P.valueUpTo Pr n x) ∧
    (∀ (n : ℕ) (x : E), (P.g x : EReal) ≤ P.J n x ∧ P.J n x ≤ P.J (n + 1) x) ∧
    (∀ (n : ℕ) (x : E), 1 ≤ n →
      P.d (n + 1) x = P.d 1 x - (P.beta : EReal) * erealIntegral (P.QX x) (fun y => max (-P.d n y) 0)) ∧
    (P.stopSet 0 = Set.univ ∧
      (∀ n : ℕ, 1 ≤ n → P.stopSet n = {x : E | 0 ≤ P.d n x}) ∧
      (∀ n : ℕ, P.stopSet (n + 1) ⊆ P.stopSet n) ∧
      IsStopTime (hitTimeCapped (fun n => P.stopSet (N - n)) N) ∧
      ∀ x : E, P.EReward Pr (hitTimeCapped (fun n => P.stopSet (N - n)) N) x = P.J N x) := by sorry

end MDPFinance.OptimalStopping
