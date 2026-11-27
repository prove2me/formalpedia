-- Prove2me | Theorems.Thm_LefebvreVariations_condorcet_domain_four_alternatives_max_nine
-- name    : LefebvreVariations.condorcet_domain_four_alternatives_max_nine
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:21:15.383483+00:00
-- url     : https://prove2.me/theorems/49ae6bcb-c011-5a9f-b6ce-b6b8bc63d701
-- title:
--   Lefebvre's variations, No. 259 — on a theme by Fishburn: a set of rankings of four alternatives with no three-voter majority cycle has at most nine rankings
-- statement:
--   Let $D$ be a set of strict rankings of four alternatives such that no profile of three voters with rankings in $D$ has a cycle $a\succ b\succ c\succ a$ in the pairwise majority relation (two of three voters). Then
--   $$|D|\le 9,$$
--   and there is such a set $D$ with $|D|=9$.
--
--   A set of rankings with no majority cycle in any profile is called a Condorcet domain, and finding the largest ones is an open research problem for general numbers of alternatives (the maxima for three, four and five alternatives are $4$, $9$ and $20$). Here the cycle condition is imposed on three-voter profiles; since the majority relation of an odd electorate is a tournament, a cycle in it contains a three-cycle on three alternatives, which is the case that the never-conditions of Condorcet domains describe, and for four alternatives the extremal size is $9$.
--
--   **Formalization Note** Rankings are \texttt{Equiv.Perm (Fin 4)} (value = rank of the alternative, lower is better), $D$ is a \texttt{Finset}, and a profile is \texttt{p : Fin 3 $\to$ Equiv.Perm (Fin 4)} with all \texttt{p v} in $D$ (repeats allowed). The statement is the conjunction of the upper bound for all such $D$ and the existence of a $D$ of size exactly $9$.
--
--   **Why this is a variation.** No open platform problem on Condorcet domains was found; this is the n = 4 case of the open question of the maximal size of a Condorcet domain (Fishburn's alternating scheme and its refutations for large n). The statement is imposed on three-voter profiles, which is exactly the triple condition behind the n = 4 value 9; it was checked by exhaustive search. No formal link to a platform parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   P. C. Fishburn, "Acyclic sets of linear orders", Social Choice and Welfare 14 (1997) 113-124, and B. Monjardet, "Acyclic domains of linear orders: a survey", in The Mathematics of Preference, Choice and Order (2009) (both cited from memory); the maximum size 9 for four alternatives is the classical value. Verified here by an exhaustive branch-and-bound over all subsets of the 24 rankings against the 392 forbidden triples of rankings (maximum 9, e.g. rankings number 0,1,2,4,6,7,8,10,13 in lexicographic order of rank vectors).

import Mathlib

namespace LefebvreVariations

/-- A set `D` of strict rankings of four alternatives such that no profile of three voters with
rankings in `D` has a cycle in the pairwise majority relation has at most nine rankings, and nine
is attained. `p v c` is the rank of alternative `c` for voter `v` (lower = better), and `a` beats
`b` when at least two of the three voters rank `a` above `b`. Source: the maximal size of a
Condorcet domain; for four alternatives it is 9 (Fishburn's alternating scheme attains it),
cited from memory from Fishburn, *Acyclic sets of linear orders*, Social Choice and Welfare 14
(1997) and Monjardet's survey (2009); the bound is also a direct exhaustive computation. -/
theorem condorcet_domain_four_alternatives_max_nine :
    (∀ D : Finset (Equiv.Perm (Fin 4)),
      (∀ p : Fin 3 → Equiv.Perm (Fin 4), (∀ v, p v ∈ D) →
        ¬ ∃ a b c : Fin 4,
          2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v a < p v b)).card ∧
          2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v b < p v c)).card ∧
          2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v c < p v a)).card) →
      D.card ≤ 9) ∧
    ∃ D : Finset (Equiv.Perm (Fin 4)), D.card = 9 ∧
      ∀ p : Fin 3 → Equiv.Perm (Fin 4), (∀ v, p v ∈ D) →
        ¬ ∃ a b c : Fin 4,
          2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v a < p v b)).card ∧
          2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v b < p v c)).card ∧
          2 ≤ (Finset.univ.filter (fun v : Fin 3 => p v c < p v a)).card := by
  sorry

end LefebvreVariations
