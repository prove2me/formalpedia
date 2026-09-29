-- Prove2me | Theorems.Thm_LocalSearchFL_KMedian_exists_pi_property_3_1
-- name    : LocalSearchFL.KMedian.exists_pi_property_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:10:50.609988+00:00
-- url     : https://prove2.me/theorems/25d9296b-6c0e-4efe-8a46-60acca728c35
-- title:
--   Property 3.1 — a bijection $\pi$ of $N_O(o)$ moving every non-capturing block $N^o_s$ off itself
-- statement:
--   Let $\sigma_S, \sigma_O : C \to F$ be assignments of the clients to facilities, with $N_O(o)$, $N_S(s)$ and $N^o_s = N_O(o) \cap N_S(s)$ as in Definition 3.1, and fix a facility $o$. Then there is a one-to-one and onto map $\pi : N_O(o) \to N_O(o)$ such that for every facility $s$ that does not capture $o$, that is $|N^o_s| \le \tfrac12 |N_O(o)|$,
--   $$\pi(N^o_s) \cap N^o_s = \emptyset.$$
--
--   This mapping lets each client $j$ served by a non-capturing facility $s$ be rerouted, when $s$ is closed, through its $O$-facility to the $S$-facility of $\pi(j)$, which differs from $s$.
--
--   **Formalization Note** The bijection of $N_O(o)$ is a permutation of all clients that maps $N_O(o)$ onto itself and fixes every client outside $N_O(o)$. The statement holds for arbitrary assignments, in particular for the nearest-facility assignments of the paper.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 549, Property 3.1 and the construction of π that follows it

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

namespace LocalSearchFL.KMedian

/-- Property 3.1 (p. 549): for a facility `o`, there is a bijection `π` of `N_O(o)` (a
permutation of the clients that fixes every client outside `N_O(o)`) such that, for every
facility `s` that does not capture `o`, `π(N^o_s) ∩ N^o_s = ∅`. -/
theorem exists_pi_property_3_1 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (o : Fa) :
    ∃ π : Equiv.Perm Cl,
      (∀ j, π j ∈ nbhd σO o ↔ j ∈ nbhd σO o) ∧
      (∀ j, j ∉ nbhd σO o → π j = j) ∧
      ∀ s : Fa, ¬ captures σS σO s o →
        ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s := by sorry

end LocalSearchFL.KMedian
