-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_proposition_7_6_11
-- name    : MDPFinance.InfiniteHorizonApplications.proposition_7_6_11
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:23.014334+00:00
-- url     : https://prove2.me/theorems/bcb7c2e8-23dd-4e2d-bb08-2a6ec23caa2b
-- title:
--   Proposition 7.6.11 — the Gittins index as a fixed point of a two-point comparison
-- statement:
--   This gives a second, computationally convenient characterization of the index: fixing a reference
--   state $i_0$ and defining $J_0(m,n) := J(m,n;I(i_0))$, the function $J_0$ is the *unique* solution
--   of a Bellman equation that only ever compares the reference state's own continuation value against
--   the current state's — and evaluating $J_0$ back at $i_0$ recovers the index $I(i_0)$ itself. This
--   fixed-point recasting is what makes the index numerically computable without solving the full
--   $K$-stopping problem for every candidate $K$.
--
--   **Moderation note.** Uniqueness is among bounded functions (Banach's fixed point theorem in $\mathbb B_b$, $b\equiv 1$), as the book's proof states; the equation has unbounded solutions.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 235, Proposition 7.6.11

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Proposition 7.6.11 (Bäuerle–Rieder, p. 235, PDF 246). Let `i_0 := (m_0,n_0) \in \mathbb N_0^2`
be fixed and define `J_0(m,n) := J(m,n;I(i_0))` for `(m,n) \in \mathbb N_0^2`. Then `J_0` is the
unique solution of `v(m,n) = \max\{p(i_0)+\beta(Pv)(i_0), p(m,n)+\beta(Pv)(m,n)\}`, `(m,n) \in
\mathbb N_0^2` (unique among bounded functions, Banach's fixed point theorem in `IB_b`, `b ≡ 1`), and
it holds `I(m_0,n_0) = J_0(m_0,n_0)`. -/
theorem proposition_7_6_11 {β : ℝ} (KS : KStoppingValue β pMN) (m0 n0 : ℕ)
    (J0 : ℕ × ℕ → ℝ) (hJ0 : J0 = fun mn => KS.J (GittinsIndex KS (m0, n0)) mn) :
    ((∀ mn, J0 mn = max (pMN (m0, n0) + β * PMN J0 (m0, n0)) (pMN mn + β * PMN J0 mn)) ∧
        ∀ v : ℕ × ℕ → ℝ, (∃ C : ℝ, ∀ mn, |v mn| ≤ C) →
          (∀ mn, v mn = max (pMN (m0, n0) + β * PMN v (m0, n0)) (pMN mn + β * PMN v mn)) →
          v = J0) ∧
      GittinsIndex KS (m0, n0) = J0 (m0, n0) := by sorry

end MDPFinance.InfiniteHorizonApplications
