-- Prove2me | Theorems.Thm_KendallQueues_GIMs_row_sums_eq_one
-- name    : KendallQueues.GIMs.row_sums_eq_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:44:43.554168+00:00
-- url     : https://prove2.me/theorems/52f73942-b22d-4c11-ba5f-286148c6f6d7
-- title:
--   §7, p. 349 — the row-sums of the GI/M/s matrix P are all equal to unity
-- statement:
--   Consider the queueing system GI/M/s with $s\ge1$ servers, inter-arrival law $A$ on $[0,\infty)$ with mean $a$, $0<a<\infty$, and negative-exponential service times of mean $b>0$. Let $P=[p_{ij}]$ be the transition matrix (8)–(14) of the chain imbedded at arrival epochs. Then every entry of $P$ is nonnegative and every row of $P$ sums to one:
--   $$p_{ij}\ge0,\qquad \sum_{j=0}^{\infty}p_{ij}=1\qquad(i=0,1,2,\dots).$$
--
--   That is, $P$ is a stochastic matrix, so that it is the transition matrix of a Markov chain on $\{0,1,2,\dots\}$; the paper uses the row-sum condition to verify the last invariance equation of the trial vector.
--
--   **Formalization Note** The statement is about the function `gimsMatrix s A b`, not about a chain, so that it is what shows a `TransitionMatrix` with this matrix exists. Nonnegativity is implicit on the page (the entries are probabilities) and is added. The row sums are stated with `HasSum`.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 349 (row sums of P)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- §7, p. 349: the entries of the GI/M/s matrix (8) are nonnegative and every row sums to one. -/
theorem row_sums_eq_one (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : IsInterarrivalLaw A a⁻¹) :
    (∀ i j, 0 ≤ gimsMatrix s A b i j) ∧ ∀ i, HasSum (fun j => gimsMatrix s A b i j) 1 := by sorry

end KendallQueues.GIMs
