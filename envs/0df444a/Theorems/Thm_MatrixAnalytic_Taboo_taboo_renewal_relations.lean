-- Prove2me | Theorems.Thm_MatrixAnalytic_Taboo_taboo_renewal_relations
-- name    : MatrixAnalytic.Taboo.taboo_renewal_relations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:42.252149+00:00
-- url     : https://prove2.me/theorems/be706e3b-742d-47ae-9e63-c6db948d94ea
-- title:
--   Theorem 5.2.3 — ${}_TR_{TD} = {}_TF_{TD}\,{}_TR_{DD}$ and ${}_TR_{DD} = \sum_{\nu\ge0}({}_TF_{DD})^\nu = (I - {}_TF_{DD})^{-1}$
-- statement:
--   Let $\{X_n\}$ be an irreducible, aperiodic Markov chain on a countable state space $S$ with transition matrix $P$. For disjoint subsets $T$ and $D$ of $S$, let ${}_TR_{ij}$ be the expected number of visits to $j$, starting from $i$, before the first visit to $T$ after time $0$, and let ${}_TF_{ij}$ be the probability, starting from $i$, of reaching $D$ at some time $\theta \ge 1$ before the first passage to $T$ and of doing so in state $j$. Then, for all disjoint $T$ and $D$ with $T$ nonempty,
--   $${}_TR_{TD} = {}_TF_{TD}\,{}_TR_{DD} \tag{5.21}$$
--   and
--   $${}_TR_{DD} = \sum_{\nu \ge 0}({}_TF_{DD})^\nu = (I - {}_TF_{DD})^{-1}, \tag{5.22}$$
--   the series converging entrywise. Explicitly: ${}_TR_{ij} = \sum_{k \in D} {}_TF_{ik}\,{}_TR_{kj}$ for $i \in T$, $j \in D$; and for $i, j \in D$, ${}_TR_{ij} = \sum_{\nu\ge0}[({}_TF_{DD})^\nu]_{ij} < \infty$.
--
--   These are the Markov renewal analogues of the renewal equations for a single state: the visits to $D$ between two visits to $T$ form a terminating Markov renewal process whose kernel is ${}_TF_{DD}$.
--
--   **Formalization Note** All quantities are probabilities or expected values in $[0, \infty]$ defined by sums over trajectories; $(I - {}_TF_{DD})^{-1}$ is, by the book's convention (p. 109), the series of powers of ${}_TF_{DD}$, and its convergence (finiteness of every entry) is a conclusion. The hypothesis that $T$ is nonempty is not printed: for $T = \emptyset$ the series in (5.22) diverges for a recurrent chain. Aperiodicity is part of the chapter's standing assumption.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 116, Theorem 5.2.3 (ₜF defined by Eq. (5.18), p. 115)

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices

namespace MatrixAnalytic.Taboo

open scoped ENNReal

/-- Latouche & Ramaswami, Theorem 5.2.3 (p. 116). Under the standing assumptions of Chapter 5
(an irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), for
any disjoint subsets `T` and `D` (with `T` nonempty):
(5.21) `ₜR_{TD} = ₜF_{TD} ₜR_{DD}`, and
(5.22) `ₜR_{DD} = Σ_{ν ≥ 0} (ₜF_{DD})^ν = (I − ₜF_{DD})⁻¹`, the series converging entrywise. -/
theorem taboo_renewal_relations {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (T D : Set S) (hT : T.Nonempty) (hTD : Disjoint T D) :
    -- (5.21)
    (∀ i ∈ T, ∀ j ∈ D, tabooR P T i j = ∑' k : D, tabooF P T D i k * tabooR P T k j) ∧
    -- (5.22)
    (∀ i ∈ D, ∀ j ∈ D,
      tabooR P T i j = seriesInv (tabooF P T D) D i j ∧ seriesInv (tabooF P T D) D i j < ⊤) := by sorry

end MatrixAnalytic.Taboo
