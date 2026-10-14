-- Prove2me | Theorems.Thm_GarrettFA_metric_net_complete_of_seq_complete
-- name    : GarrettFA.metric_net_complete_of_seq_complete
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:32:13.095035+00:00
-- url     : https://prove2.me/theorems/c534d8ea-bb8d-403f-baf6-cdae0ec3c486
-- title:
--   Prop. 4.0.1 — in metric spaces, sequential completeness implies completeness for nets
-- statement:
--   Let $(M,d)$ be a metric space in which every Cauchy sequence converges. Let $(v_i)_{i\in I}$ be a net indexed by a directed partially ordered set that is Cauchy for $d$: for every $\varepsilon>0$ there is $i_0$ with $d(v_i,v_j)<\varepsilon$ for all $i,j\ge i_0$. Then there is $x\in M$ such that
--
--   1. the net converges to $x$: for every $\varepsilon>0$ there is $i_0$ with $d(v_i,x)<\varepsilon$ for all $i\ge i_0$; and
--   2. there is a monotone sequence of indices $i_1\le i_2\le\cdots$ with $v_{i_n}\to x$.
--
--   **Formalization Note** The notes speak of "cofinal sequences converging to the same limit". A directed set need not contain a cofinal sequence, so this clause is formalized as a monotone sequence of indices along which the net converges to $x$, which is what the proof constructs.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, Proposition 4.0.1

import Mathlib

namespace GarrettFA
theorem metric_net_complete_of_seq_complete {M : Type*} [MetricSpace M]
    (hM : ∀ u : ℕ → M, CauchySeq u → ∃ x, Filter.Tendsto u Filter.atTop (nhds x))
    {I : Type*} [PartialOrder I] [IsDirected I (· ≤ ·)] (v : I → M)
    (hv : ∀ ε > 0, ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, dist (v i) (v j) < ε) :
    ∃ x : M, (∀ ε > 0, ∃ i₀ : I, ∀ i ≥ i₀, dist (v i) x < ε) ∧
      ∃ s : ℕ → I, Monotone s ∧ Filter.Tendsto (v ∘ s) Filter.atTop (nhds x) := by sorry
end GarrettFA
