-- Prove2me | Theorems.Thm_MatrixAnalytic_Taboo_sojourn_eq_series
-- name    : MatrixAnalytic.Taboo.sojourn_eq_series
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:34.521691+00:00
-- url     : https://prove2.me/theorems/7986f7d6-fb2d-4d4c-a131-684f0d0373b8
-- title:
--   Lemma 5.1.2 — $N_D = (I - P_D)^{-1} = \sum_{n\ge0}P_D^n$, the minimal nonnegative solution of $(I - P_D)N = I$ and $N(I - P_D) = I$
-- statement:
--   Let $\{X_n\}$ be an irreducible, aperiodic Markov chain on a countable state space $S$ with transition matrix $P$ (the standing assumption of Chapter 5), and let $D$ be a proper subset of $S$. Write $P_D$ for the submatrix of $P$ on $D$ and $N_D$ for the matrix of expected sojourn times in the states of $D$ before the first passage to $S \setminus D$:
--   $$[N_D]_{ij} = \sum_{n \ge 0} \mathrm P[X_n = j \;\&\; X_0, \dots, X_n \in D \mid X_0 = i], \qquad i, j \in D.$$
--   Then
--   $$N_D = (I - P_D)^{-1} = \sum_{n \ge 0} P_D^n,$$
--   every entry of this series is finite, and $N_D$ is the minimal nonnegative solution of each of the systems
--   $$(I - P_D)N = I \qquad\text{and}\qquad N(I - P_D) = I.$$
--   Precisely:
--
--   1. $[N_D]_{ij} = \sum_{n\ge0}[P_D^n]_{ij}$ and this is finite, for all $i, j \in D$;
--   2. $\sum_{k \in D} P_{ik}[N_D]_{kj} = [N_D]_{ij} - \delta_{ij}$ and $\sum_{k \in D} [N_D]_{ik}P_{kj} = [N_D]_{ij} - \delta_{ij}$, the series converging, for all $i, j \in D$;
--   3. if $X \ge 0$ is a real matrix with $\sum_{k \in D} P_{ik}X_{kj} = X_{ij} - \delta_{ij}$ for all $i, j \in D$ (or with $\sum_{k \in D} X_{ik}P_{kj} = X_{ij} - \delta_{ij}$), then $[N_D]_{ij} \le X_{ij}$ for all $i, j \in D$.
--
--   This identifies the probabilistic matrix $N_D$ with the algebraic object $(I - P_D)^{-1}$ also when $D$ is infinite, and it is the first of the book's characterizations of a matrix as a minimal solution of a matrix equation.
--
--   **Formalization Note** $N_D$ is defined as an expected value (a sum over trajectories that stay in $D$) in $[0, \infty]$, not as the series or as a solution of the system; the identity with the series and the finiteness of its entries are conclusions. The equations are stated in real numbers after converting the (finite) entries. Aperiodicity is part of the chapter's standing assumption and is kept as a hypothesis although the conclusion does not depend on it.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 109, Lemma 5.1.2 (N_D defined on p. 108; setting p. 107)

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices

namespace MatrixAnalytic.Taboo

open scoped ENNReal

/-- Latouche & Ramaswami, Lemma 5.1.2 (p. 109). Under the standing assumptions of Chapter 5 (an
irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), let `D`
be a proper subset of `S`. The matrix `N_D` of expected sojourn times in `D` before the first
passage to `S ∖ D` equals `(I − P_D)⁻¹ = Σ_{n ≥ 0} P_D^n`; this series converges (every entry is
finite); and `N_D` is the minimal nonnegative solution of each of the systems `(I − P_D)X = I`
and `X(I − P_D) = I` (rows and columns indexed by `D`, the products summing over `D`). -/
theorem sojourn_eq_series {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (D : Set S) (hD : D ≠ Set.univ) :
    -- `N_D = Σ_{n ≥ 0} P_D^n`, and the series converges
    (∀ i ∈ D, ∀ j ∈ D, sojournN P D i j = seriesInv (ennP P) D i j) ∧
    (∀ i ∈ D, ∀ j ∈ D, sojournN P D i j < ⊤) ∧
    -- `(I − P_D) N_D = I`
    (∀ i ∈ D, ∀ j ∈ D,
      HasSum (fun k : D => P i k * (sojournN P D k j).toReal)
        ((sojournN P D i j).toReal - if i = j then 1 else 0)) ∧
    -- `N_D (I − P_D) = I`
    (∀ i ∈ D, ∀ j ∈ D,
      HasSum (fun k : D => (sojournN P D i k).toReal * P k j)
        ((sojournN P D i j).toReal - if i = j then 1 else 0)) ∧
    -- minimal among nonnegative solutions of `(I − P_D) X = I`
    (∀ X : S → S → ℝ, (∀ i j, 0 ≤ X i j) →
      (∀ i ∈ D, ∀ j ∈ D,
        HasSum (fun k : D => P i k * X k j) (X i j - if i = j then 1 else 0)) →
      ∀ i ∈ D, ∀ j ∈ D, (sojournN P D i j).toReal ≤ X i j) ∧
    -- minimal among nonnegative solutions of `X (I − P_D) = I`
    (∀ X : S → S → ℝ, (∀ i j, 0 ≤ X i j) →
      (∀ i ∈ D, ∀ j ∈ D,
        HasSum (fun k : D => X i k * P k j) (X i j - if i = j then 1 else 0)) →
      ∀ i ∈ D, ∀ j ∈ D, (sojournN P D i j).toReal ≤ X i j) := by sorry

end MatrixAnalytic.Taboo
