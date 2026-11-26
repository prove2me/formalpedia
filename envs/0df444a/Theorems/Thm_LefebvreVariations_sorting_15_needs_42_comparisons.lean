-- Prove2me | Theorems.Thm_LefebvreVariations_sorting_15_needs_42_comparisons
-- name    : LefebvreVariations.sorting_15_needs_42_comparisons
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:11:18.355734+00:00
-- url     : https://prove2.me/theorems/94fefe41-8988-57df-a25b-b7e5df7e632c
-- title:
--   Lefebvre's variations, No. 161 — on a theme by Ford and Johnson: sorting 15 elements by comparisons requires 42 comparisons
-- statement:
--   For an adaptive comparison strategy $\sigma$ (the next pair $(a,b)$ to compare is a function of the list of previous answers), run on an ordering $r$ of $\{0,\dots,14\}$: the answer to a query is $[r(a)<r(b)]$. With 41 queries there are two distinct orderings $r\neq r'$ giving the same list of 41 answers (and hence the same queries):
--   $$\forall\sigma\ \exists r\neq r'\in S_{15}:\ \mathrm{hist}_{41}(\sigma,r)=\mathrm{hist}_{41}(\sigma,r').$$
--   Equivalently, sorting $15$ elements by comparisons needs at least 42 comparisons in the worst case. The information-theoretic bound gives only 41 here ($2^{41}\ge 15!$), so this is a non-trivial case; the Ford--Johnson algorithm sorts $15$ elements with 42 comparisons, so the bound is sharp.
--
--   **Formalization Note** The strategy is \texttt{List Bool $\to$ Fin n $\times$ Fin n}, the history after 41 steps is the 41-fold iterate of \texttt{h $\mapsto$ h ++ [decide (r a < r b)]} from \texttt{[]}, and orderings are \texttt{Equiv.Perm (Fin n)}. A strategy may query a pair with $a=b$ (a wasted query), which does not affect the statement.
--
--   **Why this is a variation.** There is no open platform problem on minimum-comparison sorting; this is a stand-alone finite case of the classical question of the optimality of the Ford-Johnson algorithm (open in general; known for n<=15 and n=22). At n=15 the information-theoretic bound is not sharp, so this is a first non-trivial size. No formal link to a platform parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   S(15)=42: computed by Peczarski's algorithm on a supercomputer, 2007; the value is listed in Stober and Weiss, Lower bounds for sorting 16, 17, and 18 elements (arXiv 2206.05597), and in OEIS A036604 (confirmed via search).

import Mathlib

namespace LefebvreVariations

/-- Sorting 15 elements needs 42 comparisons in the worst case (the Ford–Johnson algorithm is
optimal): no adaptive comparison strategy with only 41 comparisons separates all `15!`
orderings. A strategy `σ` picks the next pair to compare from the list of previous answers;
for an ordering `r` the run is `h ↦ h ++ [r a < r b]` iterated 41 times; two distinct
orderings with the same answer list cannot be told apart.
Source: S(12)=30 Wells 1965; S(13)=34 Kasai et al. 1994 and Peczarski, Algorithmica 40 (2004);
S(14)=38 Peczarski 2004. -/
theorem sorting_15_needs_42_comparisons (σ : List Bool → Fin 15 × Fin 15) :
    ∃ r r' : Equiv.Perm (Fin 15), r ≠ r' ∧
      (fun h : List Bool => h ++ [decide (r (σ h).1 < r (σ h).2)])^[41] [] =
      (fun h : List Bool => h ++ [decide (r' (σ h).1 < r' (σ h).2)])^[41] [] := by
  sorry

end LefebvreVariations
