-- Prove2me | Theorems.Thm_LefebvreVariations_sorting_14_needs_38_comparisons
-- name    : LefebvreVariations.sorting_14_needs_38_comparisons
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:11:00.146306+00:00
-- url     : https://prove2.me/theorems/7a85214b-dc4b-54b3-86d7-5026c56f976a
-- title:
--   Lefebvre's variations, No. 159 — on a theme by Ford and Johnson: sorting 14 elements by comparisons requires 38 comparisons
-- statement:
--   For an adaptive comparison strategy $\sigma$ (the next pair $(a,b)$ to compare is a function of the list of previous answers), run on an ordering $r$ of $\{0,\dots,13\}$: the answer to a query is $[r(a)<r(b)]$. With 37 queries there are two distinct orderings $r\neq r'$ giving the same list of 37 answers (and hence the same queries):
--   $$\forall\sigma\ \exists r\neq r'\in S_{14}:\ \mathrm{hist}_{37}(\sigma,r)=\mathrm{hist}_{37}(\sigma,r').$$
--   Equivalently, sorting $14$ elements by comparisons needs at least 38 comparisons in the worst case. The information-theoretic bound gives only 37 here ($2^{37}\ge 14!$), so this is a non-trivial case; the Ford--Johnson algorithm sorts $14$ elements with 38 comparisons, so the bound is sharp.
--
--   **Formalization Note** The strategy is \texttt{List Bool $\to$ Fin n $\times$ Fin n}, the history after 37 steps is the 37-fold iterate of \texttt{h $\mapsto$ h ++ [decide (r a < r b)]} from \texttt{[]}, and orderings are \texttt{Equiv.Perm (Fin n)}. A strategy may query a pair with $a=b$ (a wasted query), which does not affect the statement.
--
--   **Why this is a variation.** There is no open platform problem on minimum-comparison sorting; this is a stand-alone finite case of the classical question of the optimality of the Ford-Johnson algorithm (open in general; known for n<=15 and n=22). At n=14 the information-theoretic bound is not sharp, so this is a first non-trivial size. No formal link to a platform parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   M. Peczarski, New results in minimum-comparison sorting, Algorithmica 40 (2004), 133-145 (S(14)=38; confirmed via search). OEIS A036604.

import Mathlib

namespace LefebvreVariations

/-- Sorting 14 elements needs 38 comparisons in the worst case (the Ford–Johnson algorithm is
optimal): no adaptive comparison strategy with only 37 comparisons separates all `14!`
orderings. A strategy `σ` picks the next pair to compare from the list of previous answers;
for an ordering `r` the run is `h ↦ h ++ [r a < r b]` iterated 37 times; two distinct
orderings with the same answer list cannot be told apart.
Source: S(12)=30 Wells 1965; S(13)=34 Kasai et al. 1994 and Peczarski, Algorithmica 40 (2004);
S(14)=38 Peczarski 2004. -/
theorem sorting_14_needs_38_comparisons (σ : List Bool → Fin 14 × Fin 14) :
    ∃ r r' : Equiv.Perm (Fin 14), r ≠ r' ∧
      (fun h : List Bool => h ++ [decide (r (σ h).1 < r (σ h).2)])^[37] [] =
      (fun h : List Bool => h ++ [decide (r' (σ h).1 < r' (σ h).2)])^[37] [] := by
  sorry

end LefebvreVariations
