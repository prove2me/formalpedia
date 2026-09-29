-- Prove2me | Theorems.Thm_LocalSearchFL_MultiSwap_exists_pi_property_3_2
-- name    : LocalSearchFL.MultiSwap.exists_pi_property_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:41:48.524086+00:00
-- url     : https://prove2.me/theorems/b690f120-999b-45bc-80c1-ffd04facbb8d
-- title:
--   Property 3.2 — a bijection of N_O(o) moving every small class of a partition off itself
-- statement:
--   Let $N$ be a finite set, partitioned into classes: for $j \in N$ let $P_j = \{x \in N : g(x) = g(j)\}$ be the class of $j$ under a labelling $g$. Then there is a one-to-one and onto map $\pi : N \to N$ such that for every class $P$ with $|P| \le \tfrac12 |N|$,
--   $$\pi(P) \cap P = \emptyset.$$
--
--   In the analysis $N = N_O(o)$ for a facility $o \in O$, and the classes are the sets $N_S(A_i) \cap N_O(o)$ for the blocks with $|A_i| \le p$ and $N_S(s) \cap N_O(o)$ for the facilities $s$ of the blocks with $|A_i| > p$. The map $\pi$ is used to reassign the clients of the deleted facilities in each swap.
--
--   **Formalization Note** The statement is abstract (any type, any finite set $N$, any labelling $g$). The bijection of $N$ is a permutation of the ambient type that maps $N$ onto itself and fixes every point outside $N$. "$|P| \le \tfrac12|N|$" is written $2|P| \le |N|$, and $\pi(P) \cap P = \emptyset$ as $g(\pi(j)) \ne g(j)$ for every $j \in P$. This is the same abstract lemma as Property 3.1 of the single-swap mission of this series.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 553, Property 3.2 (construction as in §3.2, p. 549)

import Mathlib

namespace LocalSearchFL.MultiSwap

/-- Property 3.2 (p. 553), in abstract form. Let `N` be a finite set (the clients `N_O(o)` of a
facility `o`) partitioned into the classes of a labelling `g` (the class of `j` is
`P_j = {x ∈ N | g x = g j}`). There is a bijection `π` of `N` (a permutation fixing every point
outside `N`) such that `π(P) ∩ P = ∅` for every class `P` with `|P| ≤ ½ |N|`. -/
theorem exists_pi_property_3_2 {α β : Type} [DecidableEq β] (N : Finset α) (g : α → β) :
    ∃ π : Equiv.Perm α,
      (∀ j, π j ∈ N ↔ j ∈ N) ∧
      (∀ j, j ∉ N → π j = j) ∧
      ∀ j ∈ N, 2 * (N.filter (fun x => g x = g j)).card ≤ N.card → g (π j) ≠ g j := by sorry

end LocalSearchFL.MultiSwap
