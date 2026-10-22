-- Prove2me | Theorems.Thm_MatrixAnalytic_Taboo_taboo_visits_TcTc
-- name    : MatrixAnalytic.Taboo.taboo_visits_TcTc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:29.719921+00:00
-- url     : https://prove2.me/theorems/d3acb728-641f-4b60-a8dd-e1726ced1a84
-- title:
--   Eq. (5.23) — ${}_TR_{T^cT^c} = N_{T^c} = \sum_{\nu\ge0}P_{T^c}^\nu$
-- statement:
--   Let $\{X_n\}$ be an irreducible, aperiodic Markov chain on a countable state space $S$ with transition matrix $P$, let $T \subseteq S$ and $T^c = S \setminus T$. Let ${}_TR_{ij}$ be the expected number of visits to $j$, starting from $i$, before the first visit to $T$ after time $0$, let $N_{T^c}$ be the matrix of expected sojourn times in the states of $T^c$ before the first passage to $T$, and let $P_{T^c}$ be the submatrix of $P$ on $T^c$. Then
--   $${}_TR_{T^cT^c} = N_{T^c} = \sum_{\nu \ge 0}P_{T^c}^\nu, \tag{5.23}$$
--   that is, ${}_TR_{ij} = [N_{T^c}]_{ij} = \sum_{\nu \ge 0}[P_{T^c}^\nu]_{ij}$ for all $i, j \in T^c$.
--
--   Starting outside $T$, counting the visits to a state of $T^c$ before the first visit to $T$ is the same as counting the time spent there before leaving $T^c$; the identity with the series is the probabilistic reading of $(I - P_{T^c})^{-1}$ used throughout the book.
--
--   **Formalization Note** ${}_TR$ and $N_{T^c}$ are expected values in $[0, \infty]$ defined by sums over trajectories, the series is entrywise in $[0, \infty]$ (the book's $(I - P_{T^c})^{-1}$, p. 109), and the identities are equalities there. Aperiodicity is part of the chapter's standing assumption and is kept as a hypothesis.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 117, Eq. (5.23)

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices

namespace MatrixAnalytic.Taboo

open scoped ENNReal

/-- Latouche & Ramaswami, Eq. (5.23) (p. 117). Under the standing assumptions of Chapter 5 (an
irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), for every
subset `T` with complement `Tᶜ = S ∖ T`, `ₜR_{TᶜTᶜ} = N_{Tᶜ} = Σ_{ν ≥ 0} P_{Tᶜ}^ν`: for
`i, j ∉ T`, the expected number of visits to `j` from `i` before the first visit to `T` equals the
expected sojourn time `[N_{Tᶜ}]_{ij}` in `j` before the first passage to `T`, and both equal
`Σ_ν [P_{Tᶜ}^ν]_{ij}`. -/
theorem taboo_visits_TcTc {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (T : Set S) :
    ∀ i ∉ T, ∀ j ∉ T,
      tabooR P T i j = sojournN P Tᶜ i j ∧ sojournN P Tᶜ i j = seriesInv (ennP P) Tᶜ i j := by sorry

end MatrixAnalytic.Taboo
