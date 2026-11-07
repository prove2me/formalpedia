-- Prove2me | Theorems.Thm_MultiphaseDisj_theorem_3_1
-- name    : MultiphaseDisj.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:34.030358+00:00
-- url     : https://prove2.me/theorems/48f5fb79-1603-43ef-9c14-0c797f957185
-- title:
--   Theorem 3.1 — insert-only multiphase Disjointness needs expected query time $\Omega((\log n/\log(t_uw))^2)$
-- statement:
--   For all constants $0<c_1\le c_2$ there are $C>0$ and $n_0$ such that the following holds for every $n\ge n_0$ and every word size $w$ with $c_1\ln n\le w\le c_2\ln n$. Let $\mathcal D$ be a randomized cell-probe data structure for insert-only multiphase Disjointness with $m=n$ query sets over $[n]$, with any random tape, which has zero error, worst-case update time at most $t_u$ and expected query time at most $t_q$, where $t_u\ge1$ is an integer and $t_q\ge1$ is real. Then
--   $$
--   t_q\ \ge\ C\Big(\frac{\log n}{\log(t_uw)}\Big)^2\qquad\text{and}\qquad \max(t_u,t_q)\ \ge\ C\Big(\frac{\log n}{\log\log n}\Big)^2 .
--   $$
--
--   This is the main technical theorem of the paper: an unconditional quadratic-logarithmic lower bound in the cell-probe model for the multiphase problem of Pătrașcu with Disjointness, from which the paper's lower bounds for incremental reachability, shortest paths and other dynamic problems, and its streaming separation, follow.
--
--   **Formalization Note** The cell-probe model has $2^w$ cells of $w$ bits; operations are adaptive probe programs, and the query is read-only. Logarithms are natural. The tape is a probability space on a type in `Type`.
--
--   Differences from the source:
--   - reading: tq = Ω((log n/log(tuw))²), max(tu, tq) = Ω((log n/log log n)²), w = Θ(log n) → ∀ 0 < c₁ ≤ c₂, ∃ C > 0, ∃ n₀, ∀ n ≥ n₀, ∀ w with c₁ ln n ≤ w ≤ c₂ ln n, both bounds with constant C; reason: standard quantified reading; C and n₀ depend only on c₁, c₂
--   - encoding: logarithms (base unspecified) → natural logarithms; reason: another base changes only C, c₁, c₂
--   - encoding: worst-case update time tu (an integer) and expected query time tq, normalized tu, tq ≥ 1 → upper bounds tu ∈ ℕ, tq ∈ ℝ with 1 ≤ tu, 1 ≤ tq; reason: §2.1 'We normalize tu, tq ≥1, take tu to be an integer'
--   - encoding: [n], [m] with m = n → Fin n (0-based) for elements and query indices; reason: same instances
--   - encoding: cell-probe model with w-bit cells and addresses, free computation and workspace; the query does not write → 2^w cells BitVec w; operations are adaptive probe programs (decision trees); queries are read-only programs; reason: §2.1; a query using workspace is simulated by a read-only one with no more probes
--   - encoding: a random tape drawn independently of the input → any probability space (Ω : Type, P) shared by all operations; deterministic structures are Ω = Unit; reason: same class of structures
--   - reading: query time expected over the tape for each fixed input history → for each history the probe count is a measurable function of the tape with lower Lebesgue integral ≤ tq; reason: an expectation is taken of a random variable
--   - generalization: correctness and costs for every input history → correctness and costs required only on histories without repeated insertions; reason: a structure correct on all histories satisfies these; the hard distribution inserts distinct elements, so the bound holds for the larger class
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Theorem 3.1, p.15 (informal Theorem 1.1, p.5; conventions §2.1, p.11; proof p.24)

import Mathlib
import Definitions.Def_MultiphaseDisj_ZeroError

set_option autoImplicit false

open MeasureTheory

namespace MultiphaseDisj

/-- **Theorem 3.1 (Main theorem)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from
Disjointness*, arXiv:2610.10904, held version sha256 ba26649b…, Theorem 3.1, p.15): every
zero-error cell-probe data structure for insert-only multiphase Disjointness with `m = n` query
sets, word size `w = Θ(log n)`, worst-case update time `tu` and expected query time `tq` has
`tq = Ω((log n / log(tu w))²)`; in particular `max(tu, tq) = Ω((log n / log log n)²)`.

**Formalization Note** `w = Θ(log n)` and `Ω` are read as: for all constants `0 < c₁ ≤ c₂` there
are `C > 0` and `n₀` (depending only on `c₁, c₂`) such that for every `n ≥ n₀`, every word size
`w` with `c₁ log n ≤ w ≤ c₂ log n`, every tape probability space and every structure with the
three properties, both bounds hold with constant `C`. Logarithms are natural (another base
changes only `C`, `c₁`, `c₂`). `tu ∈ ℕ`, `tq ∈ ℝ` are upper bounds on the costs with
`tu, tq ≥ 1` (§2.1). Correctness and costs are required on histories without repeated
insertions (`ZeroError`, `UpdateCostLE`, `ExpQueryCostLE`). -/
theorem theorem_3_1 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log n ≤ w → (w : ℝ) ≤ c₂ * Real.log n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (D : DisjStructure n n w Ω) (tu : ℕ) (tq : ℝ), 1 ≤ tu → 1 ≤ tq →
        D.ZeroError → D.UpdateCostLE tu → D.ExpQueryCostLE P tq →
        C * (Real.log n / Real.log ((tu : ℝ) * w)) ^ 2 ≤ tq ∧
          C * (Real.log n / Real.log (Real.log n)) ^ 2 ≤ max (tu : ℝ) tq := by sorry

end MultiphaseDisj
