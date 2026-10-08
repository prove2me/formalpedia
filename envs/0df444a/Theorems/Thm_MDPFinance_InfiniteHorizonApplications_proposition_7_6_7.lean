-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_proposition_7_6_7
-- name    : MDPFinance.InfiniteHorizonApplications.proposition_7_6_7
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:21.261377+00:00
-- url     : https://prove2.me/theorems/d53138f3-6f11-46be-bfd1-6c795c4db58a
-- title:
--   Proposition 7.6.7 — structural properties of the K-stopping value function
-- statement:
--   As the quit-reward $K$ increases, the $K$-stopping value $J(m,n;K)$ increases, continuously and
--   convexly, while the "value of continuing" gap $J(m,n;K)-K$ shrinks; below the index $I(m,n)$,
--   continuing is strictly better and $J$ solves the Bellman recursion, while at or above the index,
--   quitting immediately is (weakly) optimal and $J(m,n;K)=K$ exactly. The value function's derivative
--   in $K$ is always between $0$ and $1$ and itself increasing — the technical backbone every
--   subsequent index property in this section is built from.
--
--   **Moderation note.** $\beta\in(0,1)$ and boundedness of $J$ come with `KStoppingValue`; the existence of the one-sided derivatives is stated.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 232, Proposition 7.6.7

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Proposition 7.6.7 (Bäuerle–Rieder, p. 232, PDF 243). Let `(m,n) \in \mathbb N_0^2` be fixed.
Then it holds: a) `K \mapsto J(m,n;K)` is increasing, continuous and convex. b) `K \mapsto
J(m,n;K) - K` is decreasing. c) `J(m,n;K) = K` if `K \ge I(m,n)`, `= p(m,n)+\beta(PJ)(m,n;K)` if
`K < I(m,n)`; in particular `K \le J(m,n;K) \le \max\{K,I(m,n)\}`. d) `K \mapsto J(m,n;K)` is a.e.
differentiable with one-sided derivatives everywhere, `0 \le \partial J/\partial K \le 1`, and
`K \mapsto \partial J/\partial K(m,n;K)` is increasing. Differentiability is rendered via
`deriv`/one-sided `derivWithin` on the co-null set where `J(m,\cdot;\cdot)` (a convex function) is
differentiable, matching Mathlib's own treatment of convex-function differentiability; the
existence of the one-sided derivatives is stated (`DifferentiableWithinAt` on `Ici K`/`Iic K`). -/
theorem proposition_7_6_7 {β : ℝ} (KS : KStoppingValue β pMN) (m n : ℕ) :
    (Monotone (KS.J · (m, n)) ∧ Continuous (KS.J · (m, n)) ∧ ConvexOn ℝ Set.univ (KS.J · (m, n))) ∧
      Antitone (fun K => KS.J K (m, n) - K) ∧
      ((∀ K, GittinsIndex KS (m, n) ≤ K → KS.J K (m, n) = K) ∧
        (∀ K, K < GittinsIndex KS (m, n) →
          KS.J K (m, n) = pMN (m, n) + β * PMN (KS.J K) (m, n)) ∧
        ∀ K, K ≤ KS.J K (m, n) ∧ KS.J K (m, n) ≤ max K (GittinsIndex KS (m, n))) ∧
      (∃ N : Set ℝ, MeasureTheory.volume N = 0 ∧
        (∀ K ∉ N, DifferentiableAt ℝ (KS.J · (m, n)) K) ∧
        (∀ K, DifferentiableWithinAt ℝ (KS.J · (m, n)) (Set.Ici K) K ∧
          DifferentiableWithinAt ℝ (KS.J · (m, n)) (Set.Iic K) K) ∧
        (∀ K, 0 ≤ derivWithin (KS.J · (m, n)) (Set.Ici K) K ∧
          derivWithin (KS.J · (m, n)) (Set.Ici K) K ≤ 1) ∧
        Monotone fun K => derivWithin (KS.J · (m, n)) (Set.Ici K) K) := by sorry

end MDPFinance.InfiniteHorizonApplications
