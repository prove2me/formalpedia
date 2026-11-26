-- Prove2me | Theorems.Thm_OnlineSaddlePoint_Supplement_theorem_6
-- name    : OnlineSaddlePoint.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:57:46.116478+00:00
-- url     : https://prove2.me/theorems/12e8252a-016c-52f7-8be4-a53741f48e6d
-- title:
--   Theorem 6 (corrected: $d_1,d_2\ge2$) — no algorithm guarantees $o(T)$ SP-Regret and $o(T)$ individual regrets for both players
-- statement:
--   Let $d_1,d_2\ge2$ and consider any deterministic algorithm for online matrix games that, in round $t$ of a game of horizon $T$, chooses $(x_t,y_t)\in\Delta_X\times\Delta_Y$ as a function of the past matrices $A_1,\dots,A_{t-1}$ (and possibly of $T$). Consider the three quantities
--
--   1. the SP-Regret $\displaystyle\Big|\sum_{t=1}^T x_t^\top A_ty_t-\min_{x\in\Delta_X}\max_{y\in\Delta_Y}\sum_{t=1}^T x^\top A_ty\Big|$, (11)
--   2. player 1's individual regret $\displaystyle\sum_{t=1}^T x_t^\top A_ty_t-\min_{x\in\Delta_X}\sum_{t=1}^T x^\top A_ty_t$, (12)
--   3. player 2's individual regret $\displaystyle\max_{y\in\Delta_Y}\sum_{t=1}^T x_t^\top A_ty-\sum_{t=1}^T x_t^\top A_ty_t$. (13)
--
--   Then the adversary can choose a single sequence $A_1,A_2,\dots$ of matrices with entries in $[-1,1]$ on which not all three quantities are $o(T)$: there is no function $f:\mathbb N\to\mathbb R$ with $f(T)/T\to0$ such that, for every horizon $T$, all three quantities (computed from $A_1,\dots,A_T$ and the algorithm's plays for horizon $T$) are at most $f(T)$. In other words, no single algorithm can guarantee sublinear SP-Regret together with sublinear individual regret for both players.
--
--   Online-learning algorithms with sublinear individual regret (such as online gradient descent or Follow-the-Leader for each player) therefore cannot, in general, also achieve sublinear SP-Regret, which is why the paper designs SP-FTL and its variants separately.
--
--   Differences from the source:
--   - generalization: "there exists an (adversarially-chosen) sequence $A_1,A_2,\dots$ such that not all of (11), (12), and (13), are true" → there is a sequence $A$ with entries in $[-1,1]$ for which no single $f$ with $f(T)/T\to0$ bounds all three quantities at every $T$; reason: if all three were $o(T)$ on $A$, their maximum would be such an $f$, so this implies the printed claim; it also implies the negation of the uniform guarantee assumed in the proof (p.27)
--   - generalization: (12) and (13) required to be $o(T)$ → (12) and (13) bounded only from above, $\le f(T)$; reason: $|q|\le f(T)$ implies $q\le f(T)$, so excluding the one-sided guarantee is the stronger impossibility; the proof only uses upper bounds
--   - correction: any numbers of actions $d_1,d_2$ (§5) → $d_1,d_2\ge2$; reason: for $d_2=1$ player 2's individual regret is $0$ and the SP-Regret equals $|$player 1's individual regret$|$, and horizon-tuned Hedge for player 1 has individual regret in $[0,O(\sqrt{T\ln d_1})]$ (nonnegative by the mix-loss bound), so all three quantities are $O(\sqrt T)$ on every sequence; symmetrically for $d_1=1$. The proof uses $d_1=d_2=2$ (recorded in DISPROOF.md)
--   - generalization: \"any algorithm that selects a sequence of $x_t,y_t$ pairs given the past payoff matrices\" → any rule `play T A t` with values in $\Delta_X\times\Delta_Y$ that is non-anticipating and may also depend on the horizon $T$ (`IsOnlineMatrixAlgorithm`); reason: horizon-independent algorithms are the special case that ignores $T$; §4.1 assumes $T$ known
--   - encoding: the entry bound $A_t\in[-1,1]^{d_1\times d_2}$ of §5 → $|(A_t)_{ij}|\le1$ for every index $t$; reason: the same condition (index $0$ is never played)
--   - encoding: $\mathbb R^{d}$ with $\|\cdot\|_1$ → `PiLp 1 (fun _ : Fin d => ℝ)`, whose norm is $\sum_i|z_i|$; reason: the same normed space
--   - encoding: $\min$, $\max$ over the simplexes → `sInf`/`sSup` of images (`minimaxValue`, `indRegretX`, `indRegretY`); reason: attained on the compact simplexes for the continuous bilinear payoffs
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Theorem 6, p.27 (proof pp.27–28)

import Mathlib
import Definitions.Def_OnlineSaddlePoint_spRegret
import Definitions.Def_OnlineSaddlePoint_Supplement_restrictedSimplex
import Definitions.Def_OnlineSaddlePoint_Supplement_bilinearPayoff
import Definitions.Def_OnlineSaddlePoint_Supplement_indRegretX
import Definitions.Def_OnlineSaddlePoint_Supplement_indRegretY
import Definitions.Def_OnlineSaddlePoint_Supplement_IsOnlineMatrixAlgorithm

namespace OnlineSaddlePoint.Supplement

open OnlineSaddlePoint Filter Topology

/-- **Theorem 6 (no algorithm has sublinear SP-Regret and sublinear individual regrets).** Rivera
Cardoso, Wang, Xu, arXiv:1806.08301v3, Theorem 6, p.27: "Consider any algorithm that selects a
sequence of `x_t, y_t` pairs given the past payoff matrices `A₁, ..., A_{t−1}`. Consider the following
three objectives: `|∑_{t=1}^T x_tᵀA_t y_t − min_{x∈Δ_X} max_{y∈Δ_Y} ∑_{t=1}^T xᵀA_t y| = o(T)` (11),
`∑_{t=1}^T x_tᵀA_t y_t − min_{x∈Δ_X} ∑_{t=1}^T xᵀA_t y_t = o(T)` (12),
`max_{y∈Δ_Y} ∑_{t=1}^T x_tᵀA_t y − ∑_{t=1}^T x_tᵀA_t y_t = o(T)` (13). Then there exists an
(adversarially-chosen) sequence `A₁, A₂, ...` such that not all of (11), (12), and (13), are true."

**Formalization Note.** The adversary chooses one infinite sequence `A₁, A₂, …` (entries in
`[−1, 1]`, the §5 setting; "for all possible sequences of matrices `{A_t}` with bounded entries
between `[−1, 1]`", p.27) after the algorithm, and on it the three quantities are not all `o(T)`:
there is no `f` with `f(T)/T → 0` such that, for every horizon `T`, (11), (12) and (13) are all at
most `f(T)`. The quantity at horizon `T` is computed from `A₁, …, A_T` and the algorithm's plays for
horizon `T`. This implies the literal "not all of (11), (12), (13) are `o(T)`" (if all three were
`o(T)`, their maximum would be such an `f`), and also the negation of the uniform worst-case
guarantee assumed in the proof. The bounds on (12), (13) are one-sided (a stronger impossibility).
The algorithm is `IsOnlineMatrixAlgorithm` (deterministic, non-anticipating, may depend on `T`).
`d₁, d₂ ≥ 2` is added: with `d₂ = 1` (or `d₁ = 1`) one individual regret vanishes and the SP-Regret
equals the absolute value of the other, so Hedge (whose regret lies in `[0, O(√T)]`) makes all three
`o(T)`; the proof uses `d₁ = d₂ = 2`. Strategies are in `PiLp 1 (fun _ : Fin d => ℝ)`;
`Δ_X = restrictedSimplex d₁ 0`. -/
theorem theorem_6 {d₁ d₂ : ℕ} (hd₁ : 2 ≤ d₁) (hd₂ : 2 ≤ d₂)
    (play : ℕ → (ℕ → Matrix (Fin d₁) (Fin d₂) ℝ) → ℕ →
      PiLp 1 (fun _ : Fin d₁ => ℝ) × PiLp 1 (fun _ : Fin d₂ => ℝ))
    (halg : IsOnlineMatrixAlgorithm play) :
    ∃ A : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ, (∀ t i j, |A t i j| ≤ 1) ∧
      ¬ ∃ f : ℕ → ℝ, Tendsto (fun T : ℕ => f T / (T : ℝ)) atTop (𝓝 0) ∧
        ∀ T : ℕ,
          spRegret (bilinearPayoff A) (restrictedSimplex d₁ 0) (restrictedSimplex d₂ 0) T
              (fun t => (play T A t).1) (fun t => (play T A t).2) ≤ f T ∧
            indRegretX (bilinearPayoff A) (restrictedSimplex d₁ 0) T
              (fun t => (play T A t).1) (fun t => (play T A t).2) ≤ f T ∧
            indRegretY (bilinearPayoff A) (restrictedSimplex d₂ 0) T
              (fun t => (play T A t).1) (fun t => (play T A t).2) ≤ f T := by sorry

end OnlineSaddlePoint.Supplement
