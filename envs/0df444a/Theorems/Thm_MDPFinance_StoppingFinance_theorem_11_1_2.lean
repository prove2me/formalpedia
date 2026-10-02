-- Prove2me | Theorems.Thm_MDPFinance_StoppingFinance_theorem_11_1_2
-- name    : MDPFinance.StoppingFinance.theorem_11_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:50:01.210787+00:00
-- url     : https://prove2.me/theorems/0f5bd74a-d9cb-44ce-9562-7db21d12b015
-- title:
--   Proposition 11.1.2 — price properties of the American put option
-- statement:
--   The price $\pi_n(x) := J_{N-n}(x)$ of an American put option has the following
--   properties:
--
--   a) $x \mapsto \pi_n(x)$ is continuous.
--   b) $x \mapsto \pi_n(x) + x$ is increasing.
--   c) $\pi_n(x)$ is decreasing in $n$ for all $x \in E$.
--   d) There exist real numbers $K =: x_N^* \ge x_{N-1}^* \ge \dots \ge x_0^* \ge 0$ such that the
--      optimal exercise time $\tau^* := \inf\{n \in \{0,\dots,N\} \mid X_n \le x_n^*\}$ is of
--      threshold type.
--
--   The book reads off what this says: "the price of the put option is increasing in the expiration
--   date and ... it is optimal to exercise if the stock falls below a certain threshold which depends
--   on the time to maturity and which is increasing when we approach the expiration date."
--
--   b) is the part that carries the argument, and it is not the obvious monotonicity: $\pi_n$ itself
--   is *decreasing* in $x$ — a put is worth less when the stock is worth more — and it is
--   $\pi_n(x) + x$ that increases. The proof uses the risk-neutral relation
--   $\beta q u + \beta(1-q)d = 1$ to rewrite the recursion as
--
--   $$ J_n(x) + x = \max\Big\{K,\ \beta\big(q(J_{n-1}(xu) + xu) + (1-q)(J_{n-1}(xd) + xd)\big)\Big\}, $$
--
--   whose right-hand side is increasing in $x$ by induction.
--
--   d) gives the thresholds explicitly, through
--
--   $$ x_n^* := \inf\Big\{x \in E \ \Big|\ \beta\big(q(\pi_{n+1}(xu) + xu) + (1-q)(\pi_{n+1}(xd) + xd)\big) \ge K\Big\}, $$
--
--   and records $x_{N-1}^* \le K$; their monotonicity in $n$ follows from c).
--
--   These thresholds are the **option exercise boundary**, a different object from the
--   credit-cancellation thresholds of Theorems 11.2.1 and 11.2.2 despite the book reusing the
--   notation $x_n^*$ for both.
--
--   **Moderation note.** The draft's d) characterised the exercise sets as `{π_n = (K−x)⁺} = {x ≤ x_n^*}`, which is false: at `n = N` (`x_N^* = K`) every `x` satisfies `J_0 = (K−x)⁺`, and for `n < N` and `x` so large that the put is worthless `π_n(x) = 0 = (K−x)⁺` with `x > x_n^*`. The exercise decision is `J_n(x) = K − x` (the book's equivalent iteration with `h(x) = K − x`, p. 333), now used; and "the optimal exercise time `τ^*` is of threshold type" is completed by the optimality of `τ^* = inf{n ≤ N | X_n ≤ x_n^*}`: it attains `sup_{τ ≤ N} 𝔼^ℚ_x[β^τ(K − S_τ)⁺] = J_N(x)`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 336 (PDF 344), Proposition 11.1.2

import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_BinomialModel

open MeasureTheory

namespace MDPFinance.StoppingFinance

/-- **Proposition 11.1.2** (p. 336). The price `π_n(x) := J_{N−n}(x)` of an American put:
a) `x ↦ π_n(x)` is continuous; b) `x ↦ π_n(x) + x` is increasing; c) `π_n(x)` is decreasing in
`n`; d) there are `K =: x_N^* ≥ x_{N−1}^* ≥ … ≥ x_0^* ≥ 0` such that the exercise sets
`{x ∈ E | π_n(x) = K − x}` are `{x ∈ E | x ≤ x_n^*}` and the threshold exercise time
`τ^* := inf{n ∈ {0,…,N} | X_n ≤ x_n^*}` is optimal: it attains `sup_{τ ≤ N} 𝔼^ℚ_x[β^τ (K−S_τ)⁺]
= J_N(x)`. -/
theorem theorem_11_1_2 (M : BinomialModel) (N : ℕ) :
    (∀ n : ℕ, ContinuousOn (M.price N n) M.E) ∧
    (∀ n : ℕ, ∀ x ∈ M.E, ∀ y ∈ M.E, x ≤ y → M.price N n x + x ≤ M.price N n y + y) ∧
    (∀ (m n : ℕ), m ≤ n → n ≤ N → ∀ x ∈ M.E, M.price N n x ≤ M.price N m x) ∧
    (∃ xstar : ℕ → ℝ,
      xstar N = M.K ∧
      (∀ n : ℕ, n < N → xstar n ≤ xstar (n + 1)) ∧
      (∀ n : ℕ, n ≤ N → 0 ≤ xstar n) ∧
      (∀ (n : ℕ) (x : ℝ), n ≤ N → x ∈ M.E → (M.price N n x = M.K - x ↔ x ≤ xstar n)) ∧
      ∀ Q : Measure (ℕ → Bool), M.IsPathLaw Q → ∀ x ∈ M.E,
        IsStoppingTime (M.thresholdTime x xstar N) ∧
        M.ERewardPlus Q x (M.thresholdTime x xstar N) = M.finiteValue Q N x ∧
        M.finiteValue Q N x = (M.J N x : EReal)) := by sorry

end MDPFinance.StoppingFinance
