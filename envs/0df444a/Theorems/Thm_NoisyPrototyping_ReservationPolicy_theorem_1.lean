-- Prove2me | Theorems.Thm_NoisyPrototyping_ReservationPolicy_theorem_1
-- name    : NoisyPrototyping.ReservationPolicy.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:04.215226+00:00
-- url     : https://prove2.me/theorems/1462e0af-c585-44dd-a215-f28f8ead053f
-- title:
--   Theorem 1, p. 11 — the fidelity-adjusted reservation price policy is optimal for sequential search with noisy measurements
-- statement:
--   Consider $N$ prototypes. Prototype $i$ has a true value $P_i$ and yields, when evaluated at cost $w_i > 0$, a noisy measurement $m_i$; the pair $(P_i, m_i)$ has a measurable joint density $f_i(P, m) \ge 0$ with $E|P_i| < \infty$, and prototypes are independent. The firm sees only measurements, evaluates prototypes one at a time in any order, may stop at any time, and launches one evaluated prototype (receiving its true value) or nothing (receiving $0$); its net payoff is that value minus the evaluation costs paid.
--
--   Let $Q_i(m) = \int P f_i(P,m)\,dP \big/ \int f_i(P,m)\,dP$ be the fidelity-adjusted expected value (1), $g_i$ the law of $X_i = Q_i(m_i)$, and $R_i$ the fidelity-adjusted reservation price, the smallest solution of
--   $$E[\max\{R, X_i\}] - R = w_i, \qquad X_i \sim g_i .$$
--   Order the prototypes so that $R_{(1)} \ge R_{(2)} \ge \cdots \ge R_{(N)}$ (ties in any way), and after evaluating the first $n$ of them let $V_n = \max\{0, Q_{(1)}(m_{(1)}), \dots, Q_{(n)}(m_{(n)})\}$ and $B_n$ the prototype attaining it ($B_n = 0$, "nothing", if every measured value is negative; among equal values the later one).
--
--   **Theorem.** The policy $\pi^*$ that, after the $n$-th evaluation ($n \in \{0, 1, \dots, N\}$), stops and accepts $B_n$ if $V_n \ge R_{(n+1)}$ (always when $n = N$), and otherwise evaluates prototype $(n+1)$, is admissible and optimal: for every admissible adaptive policy $\rho$,
--   $$\mathbb E[\text{net payoff of } \rho] \le \mathbb E[\text{net payoff of } \pi^*].$$
--
--   The optimal evaluation order is fixed in advance by indices that depend only on each prototype's cost and joint law of value and measurement, and the stopping rule compares the best fidelity-adjusted value with the next index.
--
--   **Formalization Note** The stopping rule is $\pi^*$ = `fidelityPolicy`; the paper's "if and only if" describes this rule, and strict suboptimality of the other choice is not claimed. Policies see measurements only (`History` stores no true values). Admissible = the evaluation order and final decision are measurable events and the net payoff is integrable. Disclosed readings: independence across prototypes, $E|P_i| < \infty$, $w_i > 0$, each prototype evaluated at most once, stopping after the $N$-th evaluation; formula (1) with $dP$ in the denominator (the page prints $dm$); $g_i$ as the push-forward law of $Q_i(m_i)$. $R_i$ is given by the hypothesis that it is the least root, not by a choice function. The $0$-based index `σ n` is the paper's $(n+1)$.
-- source:
--   Bhaskaran and Erat, Optimal Prototyping with Noisy Measurements, author manuscript of 6 Nov 2024 (MSOM 2025, doi:10.1287/msom.2024.1133), p. 11, Theorem 1 (with (1), (2), R_i p. 10 and V_i, B_i p. 11)

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model

namespace NoisyPrototyping.ReservationPolicy
open MeasureTheory
theorem theorem_1 {N : ℕ} (M : Model N) (f : Fin N → ℝ × ℝ → ℝ)
    (hf_nonneg : ∀ i z, 0 ≤ f i z) (hf_meas : ∀ i, Measurable (f i))
    (hlaw : ∀ i, M.law i =
      (volume : Measure (ℝ × ℝ)).withDensity (fun z => ENNReal.ofReal (f i z)))
    (R : Fin N → ℝ)
    (hR : ∀ i, IsLeast {r : ℝ | ∫ x, max (x - r) 0 ∂(g M.toSearchProblem (fun j => Q (f j)) i)
      = M.cost i} (R i))
    (σ : Fin N ≃ Fin N) (hσ : ∀ a b, a ≤ b → R (σ b) ≤ R (σ a)) :
    Admissible M.toSearchProblem (fidelityPolicy (fun j => Q (f j)) σ R) ∧
    ∀ ρ : Policy N, Admissible M.toSearchProblem ρ →
      value M.toSearchProblem ρ ≤
        value M.toSearchProblem (fidelityPolicy (fun j => Q (f j)) σ R) := by sorry
end NoisyPrototyping.ReservationPolicy
