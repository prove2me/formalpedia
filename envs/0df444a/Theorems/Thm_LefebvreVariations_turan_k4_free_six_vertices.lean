-- Prove2me | Theorems.Thm_LefebvreVariations_turan_k4_free_six_vertices
-- name    : LefebvreVariations.turan_k4_free_six_vertices
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:11:23.623921+00:00
-- url     : https://prove2.me/theorems/6ba0d377-9df9-5f20-a3f2-7d9189130369
-- title:
--   Lefebvre's variations, No. 162 — on a theme by Turán: a 3-uniform hypergraph on 6 vertices with no K_4^(3) has at most 14 edges
-- statement:
--   $$\forall H\subseteq \tbinom{[6]}{3}:\quad \bigl(\nexists S\subseteq[6],\ |S|=4,\ \tbinom{S}{3}\subseteq H\bigr)\ \Longrightarrow\ |H|\le 14.$$
--
--   Every family of triples of an 6-element set in which no 4 points span all 4 of their triples has at most $14$ members. The bound is sharp: Turán's construction with parts of sizes $2,2,2$ (8 transversal triples plus 6 triples of type 2+1) has exactly $14$ triples. Together with the values $3,7,14,23$ for $n=4,\dots,7$, this is the exact version of Turán's problem for the smallest sizes.
--
--   **Formalization Note** `H : Finset (Finset (Fin 6))` with every member of cardinality $3$ and no $S$ with `S.card = 4 ∧ S.powersetCard 3 ⊆ H`, exactly as in `turan_problem_3_uniform`; the conclusion is `H.card ≤ 14`.
--
--   **Why this is a variation.** This is a variation of the open Turán problem for 3-uniform hypergraphs (platform problem turan_problem_3_uniform), whose parent asks for the asymptotic density of K_4^(3)-free triple systems. It is the exact finite value at n = 6, in the parent's own definitions (triples as Finset, forbidden S with S.powersetCard 3 ⊆ H). It is a first non-trivial size: a prover can settle it by a finite case analysis, and the sharp values here are the base cases of Turán's construction. No formal link to the asymptotic statement is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   P. Turán (1941), Turán's hypergraph problem, as in the platform problem turan_problem_3_uniform. Exact small values ex(n,K_4^(3)) = 3, 7, 14, 23 for n = 4..7 (matching Turán's construction) were computed here by exhaustive branch-and-bound search; literature values e.g. in Sidorenko, 'What we know and what we do not know about Turán numbers', Graphs and Combinatorics 11 (1995) (cited from memory).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Turán's 3-uniform problem at `n = 6`: a family of triples of a 6-set with no 4 vertices spanning all 4 triples has at most 14 members. The bound is attained by Turán's construction on parts of sizes 2, 2, 2 (8 transversal triples plus 6 triples of type 2+1 along the cyclic order). The value 14 was confirmed by exhaustive search; it agrees with the values 3, 7, 14, 23 of Turán's conjecture for n = 4..7.
Source: P. Turán (1941), the problem as stated in the parent platform problem `turan_problem_3_uniform`; small exact values e.g. in Sidorenko, "What we know and what we do not know about Turán numbers", Graphs Combin. 11 (1995) (cited from memory). -/
theorem turan_k4_free_six_vertices (H : Finset (Finset (Fin 6)))
    (h3 : ∀ e ∈ H, e.card = 3)
    (hK4 : ¬∃ S : Finset (Fin 6), S.card = 4 ∧ S.powersetCard 3 ⊆ H) :
    H.card ≤ 14 := by
  sorry

end LefebvreVariations
