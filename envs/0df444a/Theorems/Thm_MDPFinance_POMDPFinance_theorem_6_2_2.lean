-- Prove2me | Theorems.Thm_MDPFinance_POMDPFinance_theorem_6_2_2
-- name    : MDPFinance.POMDPFinance.theorem_6_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:36:32.713801+00:00
-- url     : https://prove2.me/theorems/c30f1537-0f1e-471d-9c3a-0ce4d2f81144
-- title:
--   Theorem 6.2.2 — explicit solution of QP(b) under partial observation
-- statement:
--   This theorem solves the auxiliary quadratic-loss problem $QP(b)$ — minimize $\mathbb E^\pi_{x_0}
--   [(X_N-b)^2]$ — that Section 6.2's Lagrangian embedding of the mean-variance problem reduces to,
--   the partial-observation analogue of chunk `04c`'s Theorem 4.6.5. The value function factors as
--   $$
--   V_n(x,\rho) = \Big(\frac{xS^0_N}{S^0_n} - b\Big)^2 d_n(\rho),
--   $$
--   with $(d_n)$ the recursion (6.7) of `MDPFinance.POMDPFinance.dRem`, and the minimizing portfolio
--   is explicit:
--   $$
--   f_n^*(x,\rho) = \Big(\frac{bS^0_n}{S^0_N} - x\Big) C_{n+1}(\rho)^{-1}\ell_{n+1}(\rho).
--   $$
--   The Markov strategy built from these decision rules attains the infimum value of part (a) at
--   every initial wealth $x_0$, and the theorem additionally identifies the first and second moment
--   of terminal wealth this optimal strategy achieves, $\mathbb E^{\pi^*}_{x_0}[X_N] = x_0S^0_N
--   d_0(Q_0) + b(1-d_0(Q_0))$ and the analogous second-moment formula, feeding directly into the
--   mean-variance solution of Theorem 6.2.3.
--
--   **Formalization Note.** Part (a)'s value function, indexed by an arbitrary absolute time $n$, is
--   obtained from the shared value-function scaffold by reindexing the (non-stationary) rate sequence
--   to start at $n$, rather than introducing a second, separately time-indexed value-function
--   construction.
--
--   **Moderation note.** Under Assumption (FM) and the rates of `MeanVarianceMarket`, for $\rho\in\mathbb P(E_Y)$; the draft had no assumptions at all (the inverse in (6.7) is then a default value and the value formula fails).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 186, Theorem 6.2.2

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
import Definitions.Def_MDPFinance_POMDPFinance_MeanVariance

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- Theorem 6.2.2 (Bäuerle–Rieder, p. 186, PDF 199). For the solution of the Markov Decision
Problem `QP(b)` it holds: a) The value functions are given by `V_n(x,\rho) =
((xS^0_N/S^0_n)-b)^2 d_n(\rho)`, `(x,\rho) \in E_X \times ℙ(E_Y)` where `(d_n)` is defined in
(6.7) (`V_n(x,\rho)` rendered as `Jinf` over the remaining `N-n` stages, rates reindexed to start
at `n`, matching `Jinf`'s own "stages-from-here" convention). Then `V_0(x_0,Q_0)` is the value of
`QP(b)` (a special case of the same formula, not restated separately, as in `theorem_6_1_1`). b)
Let `f_n^*(x,\rho) := (bS^0_n/S^0_N - x) \, C_{n+1}(\rho)^{-1}\ell_{n+1}(\rho)`, `(x,\rho) \in E_X
\times ℙ(E_Y)`. Then the portfolio strategy `\pi^* = (f_0,\dots,f_{N-1})` is optimal for `QP(b)`
where `f_n(h_n) := f_n^*(x_n,\mu_n(\cdot|h_n))` (attains the infimum value of a)). c) The first
and second moment of `X_N` under `\pi^*` are given by `𝔼^{\pi^*}_{x_0}[X_N] = x_0S^0_Nd_0(Q_0) +
b(1-d_0(Q_0))`, `𝔼^{\pi^*}_{x_0}[X_N^2] = (x_0S^0_N)^2d_0(Q_0) + b^2(1-d_0(Q_0))`. The section's
standing Assumption (FM) and the rates are the fields of `MeanVarianceMarket`; state claims for
`ρ ∈ ℙ(E_Y)`. -/
theorem theorem_6_2_2 {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (Mv : MeanVarianceMarket M) (N : ℕ) (b : ℝ) :
    (∀ n ≤ N, ∀ x, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
        Jinf M Fd (fun j => Mv.i (n + j)) (fun x => (x - b) ^ 2) (fun _ => Set.univ)
        (N - n) x ρ =
          (((S0 Mv.i N / S0 Mv.i n * x - b) ^ 2 * dRem M Fd (N - n) ρ : ℝ) : EReal)) ∧
      (let fs : ℕ → ℝ × Measure EY → Fin d → ℝ := fun n xρ =>
          (b * S0 Mv.i n / S0 Mv.i N - xρ.1) •
            (CRem M Fd (N - n - 1) xρ.2)⁻¹.mulVec (lRem M Fd (N - n - 1) xρ.2)
        ∀ x0, Vpi M Fd Mv.i (fun x => (x - b) ^ 2) (ofMarkov M Fd Mv.i x0 fs) N 0 (fun _ => 0)
              x0 M.Q0 =
            Jinf M Fd Mv.i (fun x => (x - b) ^ 2) (fun _ => Set.univ) N x0 M.Q0 ∧
          EXN M Fd Mv.i (ofMarkov M Fd Mv.i x0 fs) N x0 =
            ((x0 * S0 Mv.i N * dRem M Fd N M.Q0 + b * (1 - dRem M Fd N M.Q0) : ℝ) : EReal) ∧
          EXN2 M Fd Mv.i (ofMarkov M Fd Mv.i x0 fs) N x0 =
            (((x0 * S0 Mv.i N) ^ 2 * dRem M Fd N M.Q0 + b ^ 2 * (1 - dRem M Fd N M.Q0) : ℝ) :
              EReal)) := by sorry

end MDPFinance.POMDPFinance
