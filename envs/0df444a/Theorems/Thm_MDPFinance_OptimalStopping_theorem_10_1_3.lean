-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_1_3
-- name    : MDPFinance.OptimalStopping.theorem_10_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:41:51.983625+00:00
-- url     : https://prove2.me/theorems/83bb8a65-0cc5-4f23-9ab4-94fd40ed374f
-- title:
--   Theorem 10.1.3 — the finite-horizon Bellman recursion for stopping
-- statement:
--   **Theorem 10.1.3** (p. 306). Suppose a stopping problem with finite horizon $N$ is given.
--   Then it holds:
--
--   a) $V_N = g_N$ and $V_n = \mathcal{T}_n V_{n+1}$ for $n = N-1,\dots,0$ where
--      $\mathcal{T}_n v(x) = \max\{g_n(x),\ c_n(x) + \int v(x')Q^X_n(dx'|x)\}$, $x \in E$.
--   b) Let $f_n^*(x) := 1$ if $V_n(x) = g_n(x)$ and $f_n^*(x) := 0$ otherwise. Then
--      $(f_0^*,f_1^*,\dots,f_{N-1}^*)$ is an optimal policy and the stopping time
--      $\tau^* := \min\{n \in \mathbb{N}_0 \mid V_n(X_n) = g_n(X_n)\}$ is optimal for the stopping
--      problem **(10.1)**.
--
--   a) is stated as the existence of a family $V$ that both satisfies the recursion **and** is, at each
--   $n$, the least upper bound of the values achievable from time $n$. Stating only the recursion would
--   restate a definition rather than prove a theorem: the content is that the *value* of the stopping
--   problem over $[n,N]$ satisfies it. The least-upper-bound clause also pins $V$ uniquely, so the
--   existential is not a weakening.
--
--   b)'s $\tau^*$ is the first time the value function touches the stopping reward — stop as soon as
--   waiting is worth nothing more.
--
--   **Moderation note.** The draft asserted the existence of *some* family `V` satisfying the recursion and the supremum property; now `V_n` is the value over `[n,N]` itself, a) is `V_N = g_N`, `V_n = T_n V_{n+1}` in `[-∞,∞]`, and b) is optimality of `τ^* = min{n | V_n(X_n) = g_n(X_n)} ∧ N` as attainment of `V_0`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 306 (PDF 314), Theorem 10.1.3

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_StoppingProblem

open MeasureTheory

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.1.3** (p. 306). a) `V_N = g_N` and `V_n = T_n V_{n+1}` for `n = N-1,…,0`, where
`V_n` is the value of the stopping problem over `[n,N]`. b) `τ^* := min{n | V_n(X_n) = g_n(X_n)}`
(capped at `N`) is an optimal stopping time for **(10.1)**, and the policy `f_n^* = 1_{V_n = g_n}`
is optimal. -/
theorem theorem_10_1_3 {E : Type*} [MeasurableSpace E] {N : ℕ} (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr) :
    ((∀ x, P.Vn Pr N x = (P.g N x : EReal)) ∧
      ∀ n : ℕ, n < N → ∀ x, P.Vn Pr n x = P.T n (P.Vn Pr (n + 1)) x) ∧
    (IsStopTime (hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N) ∧
      (∀ w : ℕ → E, hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N w ≤ (N : ℕ∞)) ∧
      ∀ x : E, P.EReward Pr 0 (hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N) x
        = P.Vn Pr 0 x) := by sorry

end MDPFinance.OptimalStopping
