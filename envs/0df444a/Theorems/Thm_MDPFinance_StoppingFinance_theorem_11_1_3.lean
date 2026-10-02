-- Prove2me | Theorems.Thm_MDPFinance_StoppingFinance_theorem_11_1_3
-- name    : MDPFinance.StoppingFinance.theorem_11_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:49:48.204985+00:00
-- url     : https://prove2.me/theorems/476f5f90-4fbd-4af7-8ada-2f85844554b8
-- title:
--   Theorem 11.1.3 — the value of the perpetual American put option
-- statement:
--   The prefix 'perpetual' refers to the fact that the put has no expiration date, i.e. the
--   stopping problem has an unbounded horizon; the price at time zero is
--   $P(x) := \sup_{\tau \le \infty} \mathbb{E}^{\mathbb{Q}}_x[\beta^\tau(K - S_\tau)]$, where the
--   stopping reward for $\tau = \infty$ is equal to zero.
--
--   a) The value $P(x)$ of the perpetual American put option with strike $K$ and initial stock price
--      $x > 0$ is given by $J(x) = \lim_{n\to\infty} J_n(x)$.
--   b) $P$ is a solution of the equation
--      $P(x) = \max\{(K-x)^+,\ \beta(qP(xu) + (1-q)P(xd))\} =: \mathcal{T}P(x)$
--      and $0 \le P(x) \le K$ for $x \in E$.
--   c) $P$ is the smallest superharmonic function which majorizes $(K-x)^+$, i.e. $P$ is the smallest
--      solution of $P(x) \ge (K-x)^+$, $P(x) \ge \beta(qP(xu) + (1-q)P(xd))$, $x \in E$.
--   d) Let $E^* := \{x \in E \mid P(x) = (K-x)^+\}$ and $f^*(x) = 1_{E^*}(x)$. Moreover, let
--      $J_{f^*} := \lim_{n\to\infty}\mathcal{T}_{f^*}^n 0$. **If $J_{f^*} \ge \mathcal{T}J_{f^*}$**
--      then $P(x) = J_{f^*}(x)$ for $x \in E$ and $\tau^* := \inf\{n \in \mathbb{N}_0 \mid X_n \in E^*\}$
--      is an optimal exercise time.
--
--   This is the option-pricing instance of the general unbounded-horizon stopping theory: $P$ is
--   characterised exactly as the smallest superharmonic majorant of the payoff, now for $(K-x)^+$.
--
--   Four things in the statement are load-bearing.
--
--   **$0 \le P(x) \le K$ in b) is a genuine claim, not a side remark.** The fixed point equation
--   $\mathcal{T}P = P$ alone has other solutions; it is boundedness together with c)'s minimality that
--   pins $P$ down among them.
--
--   **c) is a minimality statement**, so it quantifies over every superharmonic majorant. Stating only
--   that $P$ is *a* superharmonic majorant would be the easy half.
--
--   **d) is conditional.** The hypothesis $J_{f^*} \ge \mathcal{T}J_{f^*}$ is the book's own and is not
--   automatic: without it the exercise region $E^*$ need not deliver an optimal stopping time. An
--   unconditional version would be a different — and false — theorem.
--
--   **d)'s second half is an attainment claim.** "$\tau^*$ is an optimal exercise time" is formalized
--   as: $\tau^*$ is a stopping time, its discounted reward is integrable, and its expectation *equals*
--   $P(x)$. Asserting only that $\tau^*$ is a stopping time, or only $\le P(x)$, would be the trivial
--   half — every stopping time's value is $\le P(x)$ by definition of the supremum.
--
--   **Moderation note.** The draft omitted part e) (`E^* = {x ∈ E | x ≤ x^*}` for some `x^* ∈ [0,K]`) and carried `P` and `J_{f^*}` as free functions with `IsLUB`/limit hypotheses; now `P` is the perpetual value, `J := sup_n J_n`, `J_{f^*} := sup_n 𝒯_{f^*}^n 0`, a) is `P = J = lim J_n`, d) is conditional as in the book with optimality as attainment of `P` (reward `0` on `{τ^* = ∞}`), and e) is stated.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 337 (PDF 345), Theorem 11.1.3

import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_BinomialModel

open MeasureTheory Filter Topology

namespace MDPFinance.StoppingFinance

/-- **Theorem 11.1.3** (pp. 337-338), the perpetual American put `P(x) := sup_{τ ≤ ∞}
𝔼^ℚ_x[β^τ (K − S_τ)]` (reward `0` on `{τ = ∞}`). a) `P(x) = J(x) = lim_n J_n(x)` for `x ∈ E`.
b) `P = 𝒯P` and `0 ≤ P ≤ K` on `E`. c) `P` is the smallest superharmonic majorant of `(K−x)⁺`.
d) With `E^* := {x ∈ E | P(x) = (K−x)⁺}` and `J_{f^*} := lim_n 𝒯_{f^*}^n 0`: if `J_{f^*} ≥ 𝒯J_{f^*}`
then `P = J_{f^*}` on `E` and `τ^* := inf{n | X_n ∈ E^*}` is an optimal exercise time. e) There is
`x^* ∈ [0,K]` with `E^* = {x ∈ E | x ≤ x^*}`. -/
theorem theorem_11_1_3 (M : BinomialModel) (Q : Measure (ℕ → Bool)) (hQ : M.IsPathLaw Q) :
    (∀ x ∈ M.E, M.perpetualValue Q x = (M.Jlim x : EReal) ∧
      Tendsto (fun n => M.J n x) atTop (𝓝 (M.Jlim x))) ∧
    ((∀ x ∈ M.E, M.Jlim x = M.T M.Jlim x) ∧ ∀ x ∈ M.E, 0 ≤ M.Jlim x ∧ M.Jlim x ≤ M.K) ∧
    (M.Superharmonic M.Jlim ∧ (∀ x ∈ M.E, M.payoff x ≤ M.Jlim x) ∧
      ∀ V : ℝ → ℝ, M.Superharmonic V → (∀ x ∈ M.E, M.payoff x ≤ V x) →
        ∀ x ∈ M.E, M.Jlim x ≤ V x) ∧
    ((∀ x ∈ M.E, M.T (M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) x ≤
        M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} x) →
      ∀ x ∈ M.E, M.Jlim x = M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} x ∧
        IsStoppingTime (M.exerciseTime x {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) ∧
        M.EReward Q x (M.exerciseTime x {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) =
          M.perpetualValue Q x) ∧
    (∃ xstar : ℝ, 0 ≤ xstar ∧ xstar ≤ M.K ∧
      {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} = {y | y ∈ M.E ∧ y ≤ xstar}) := by sorry

end MDPFinance.StoppingFinance
