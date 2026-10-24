-- Prove2me | Theorems.Thm_MatrixAnalytic_Taboo_limiting_vector_taboo
-- name    : MatrixAnalytic.Taboo.limiting_vector_taboo
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:39.283799+00:00
-- url     : https://prove2.me/theorems/29545917-1cdc-47e2-bf88-6f675e358a80
-- title:
--   Theorem 5.2.1 — $\boldsymbol\pi_D = \boldsymbol\pi_T\,{}_TR_{TD}$ for disjoint subsets $T$ and $D$
-- statement:
--   Let $\{X_n\}$ be an irreducible, aperiodic Markov chain on a countable state space $S$ with transition matrix $P$, and let $\boldsymbol\pi$ be its limiting probability vector,
--   $$\pi_j = \lim_{k \to \infty} \mathrm P[X_k = j \mid X_0 = i] \qquad \text{for all } i, j \in S.$$
--   For subsets $T$, $D$ of $S$, let ${}_TR_{TD}$ be the matrix of expected numbers of visits to the states of $D$ between two visits to $T$: ${}_TR_{ij}$, for $i \in T$ and $j \in D$, is the expected number of visits to $j$, starting from $i$, before the first return to $T$. Then for all disjoint subsets $T$ and $D$ with $T$ nonempty,
--   $$\boldsymbol\pi_D = \boldsymbol\pi_T\,{}_TR_{TD}, \qquad\text{i.e.}\qquad \pi_j = \sum_{i \in T} \pi_i\,{}_TR_{ij} \quad\text{for every } j \in D. \tag{5.6}$$
--
--   This generalizes the relation $\pi_n = \pi_{n-1}R_n$ for birth-and-death chains to arbitrary subsets of states, and it is the identity on which the matrix-geometric property of later chapters rests.
--
--   **Formalization Note** The limiting vector is given as a hypothesis by its defining limits, which exist for every irreducible aperiodic chain (in the null recurrent and transient cases $\boldsymbol\pi = 0$). The identity is stated in $[0, \infty]$ (probabilities read through `ENNReal.ofReal`), so the right-hand side always exists. The hypothesis that $T$ is nonempty is not printed: for $T = \emptyset$ the right-hand side is an empty sum while $\pi_j > 0$ for a positive recurrent chain, so the printed statement fails there.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 112, Theorem 5.2.1 (setting p. 107; ₜR defined by Eq. (5.5), p. 111)

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices

namespace MatrixAnalytic.Taboo

open scoped ENNReal

/-- Latouche & Ramaswami, Theorem 5.2.1 (p. 112). Under the standing assumptions of Chapter 5
(an irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), let
`π` be its limiting probability vector, `π_j = lim_{k → ∞} P[X_k = j | X_0 = i]` for all `i`.
Then for all disjoint subsets of states `T` and `D` (with `T` nonempty),
`π_D = π_T ₜR_{TD}` (5.6), i.e. `π_j = Σ_{i ∈ T} π_i ₜR_{ij}` for every `j ∈ D`, where `ₜR_{TD}`
records the expected numbers of visits to the states of `D` between two visits to `T`. -/
theorem limiting_vector_taboo {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (π : S → ℝ)
    (hlim : ∀ i j : S, Filter.Tendsto (fun k => stepPow P k i j) Filter.atTop (nhds (π j)))
    (T D : Set S) (hT : T.Nonempty) (hTD : Disjoint T D) :
    ∀ j ∈ D, ENNReal.ofReal (π j) = ∑' i : T, ENNReal.ofReal (π i) * tabooR P T i j := by sorry

end MatrixAnalytic.Taboo
