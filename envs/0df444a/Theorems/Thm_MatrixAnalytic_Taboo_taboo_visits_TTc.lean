-- Prove2me | Theorems.Thm_MatrixAnalytic_Taboo_taboo_visits_TTc
-- name    : MatrixAnalytic.Taboo.taboo_visits_TTc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:28.58461+00:00
-- url     : https://prove2.me/theorems/6c678198-4151-4c76-8a5e-4fe02bb1115e
-- title:
--   Eq. (5.11) — ${}_TR_{TT^c} = P_{TT^c}N_{T^c}$
-- statement:
--   Let $\{X_n\}$ be an irreducible, aperiodic Markov chain on a countable state space $S$ with transition matrix $P$, let $T \subseteq S$ and $T^c = S \setminus T$. For $i \in T$ and $j \in T^c$ let ${}_TR_{ij}$ be the expected number of visits to $j$, starting from $i$, before the first return to $T$, and let $N_{T^c}$ be the matrix of expected sojourn times in the states of $T^c$ before the first passage to $T$. Then
--   $${}_TR_{TT^c} = P_{TT^c}N_{T^c}, \tag{5.11}$$
--   that is,
--   $${}_TR_{ij} = \sum_{k \in T^c} P_{ik}\,[N_{T^c}]_{kj} \qquad\text{for all } i \in T,\ j \in T^c.$$
--
--   Together with Theorem 5.2.1 this expresses the stationary probabilities outside $T$ through those in $T$, the one-step transitions out of $T$ and the sojourn-time matrix of the complement; it is the step that turns Theorem 5.2.1 into the formula for the restricted chain.
--
--   **Formalization Note** ${}_TR$ and $N_{T^c}$ are expected values in $[0, \infty]$ defined by sums over trajectories, and the identity is an equality there; the transition probabilities enter through `ENNReal.ofReal`. Aperiodicity is part of the chapter's standing assumption and is kept as a hypothesis.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 113, Eq. (5.11)

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices

namespace MatrixAnalytic.Taboo

open scoped ENNReal

/-- Latouche & Ramaswami, Eq. (5.11) (p. 113). Under the standing assumptions of Chapter 5 (an
irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), for every
subset `T` with complement `Tᶜ = S ∖ T`, `ₜR_{TTᶜ} = P_{TTᶜ} N_{Tᶜ}`: for `i ∈ T` and `j ∉ T`,
the expected number of visits to `j` before the first return to `T` is
`Σ_{k ∈ Tᶜ} P_{ik} [N_{Tᶜ}]_{kj}`, where `N_{Tᶜ}` records the expected sojourn times in `Tᶜ`
before the first passage to `T`. -/
theorem taboo_visits_TTc {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (T : Set S) :
    ∀ i ∈ T, ∀ j ∉ T,
      tabooR P T i j = ∑' k : (Tᶜ : Set S), ennP P i k * sojournN P Tᶜ k j := by sorry

end MatrixAnalytic.Taboo
