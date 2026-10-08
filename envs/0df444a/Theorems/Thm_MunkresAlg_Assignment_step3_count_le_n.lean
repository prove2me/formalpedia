-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_step3_count_le_n
-- name    : MunkresAlg.Assignment.step3_count_le_n
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:11:51.652182+00:00
-- url     : https://prove2.me/theorems/8365ad76-38c1-4d83-9d82-90edefb5a607
-- title:
--   §1, finiteness paragraph, p. 35 — after at most n applications of Step 3 the maximal number of independent zeros increases
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $s^{(0)},s^{(1)},\dots,s^{(L)}$ be a finite piece of a run of Munkres' algorithm (each state is obtained from the previous one by a move) whose first state is reachable from $A$. Let $m$ be a natural number, and suppose that at every state $s^{(\ell)}$ of the piece that is at Step 3, the maximal number of independent zeros of its matrix equals $m$. Then
--   $$
--   \#\{\ell : s^{(\ell)} \text{ is at Step 3}\}\le n .
--   $$
--   In the paper's words: after at most $n$ applications of Step 3, the maximal number of (independent) zeros in the matrix must be increased.
--
--   Combined with the monotonicity $n_{k+1}\ge n_k$ and the bound $n_k\le n$, this gives the finiteness of the algorithm for real matrices, without the integrality assumption of p. 32.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 35, §1, finiteness paragraph

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, finiteness paragraph, p. 35: along any finite piece of a run starting at a reachable
state, if the maximal number of independent zeros is the same value `m` at every Step 3 state of
the piece, then Step 3 is applied at most `n` times in it. -/
theorem step3_count_le_n {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ss : List (State n))
    (hchain : List.IsChain Step ss) (hhead : ∀ s ∈ ss.head?, Reachable A s) (m : ℕ)
    (hm : ∀ s ∈ ss, s.phase = Phase.step3 → maxIndepZeros s.A = m) :
    (ss.filter (fun s => s.phase = Phase.step3)).length ≤ n := by sorry

end MunkresAlg.Assignment
