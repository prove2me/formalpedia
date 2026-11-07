-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_B_5
-- name    : OnlineBinCover.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:11.142195+00:00
-- url     : https://prove2.me/theorems/22e31622-ffef-4e32-a054-b41f06c55ad2
-- title:
--   Lemma B.5 — greedy covering of small slots
-- statement:
--   Let $S,M$ be disjoint sets of items with every item of $M$ at least as large as every item of $S$. Let $0\le d_1\le\dots\le d_b$ be slot demands with
--
--   $$\sum_{j=1}^bd_j\le\mathrm{vol}(S),\qquad b\le|M|.$$
--
--   Then filling the slots one at a time in this order, each item going to the first slot whose demand is not yet met, covers all $b$ slots when the items of $S\cup M$ arrive in any order.
--
--   The lemma is the covering argument of Csirik, Johnson and Kenyon in a form that permits any arrival order; it is how medium items make up for the indivisibility of small items.
--
--   Differences from the source:
--   - generalization: items with sizes in $(0,1]$ → items with nonnegative sizes; reason: the proof uses only nonnegativity; specializes to the paper's items
--   - encoding: "using the items of $S\cup M$ in any order" → every duplicate-free list enumerating $S\cup M$; reason: an order is such a list
--   - encoding: filling slots one at a time in increasing demand order → each item to the first slot whose load is below its demand; zero-demand slots are met from the start; reason: the paper omits zero-demand slots as already covered
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma B.5, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_OnlineBinCover_Basic
import Definitions.Def_OnlineBinCover_Greedy

namespace OnlineBinCover

/-- Lemma B.5 (Greedy covering of small slots), p.22. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

Let `S, M` be disjoint item sets with every item of `M` at least as large as every item of `S`. If
`0 ≤ d₁ ≤ ⋯ ≤ d_b`, `∑_j d_j ≤ vol(S)` and `b ≤ |M|`, then filling the slots one at a time in this
order (each item to the first slot whose demand is not yet met) covers all `b` slots, using the items
of `S ∪ M` in any order. -/
theorem lemma_B_5 {n b : ℕ} (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i) (S M : Finset (Fin n))
    (hSM : Disjoint S M) (hMS : ∀ a ∈ M, ∀ c ∈ S, s c ≤ s a) (d : Fin b → ℝ)
    (hd0 : ∀ j, 0 ≤ d j) (hdm : Monotone d) (hsum : ∑ j, d j ≤ volOn s S) (hb : b ≤ M.card)
    (order : List (Fin n)) (hnd : order.Nodup) (hord : order.toFinset = S ∪ M) :
    ∀ j, d j ≤ greedyLoads d (order.map s) j := by sorry

end OnlineBinCover
