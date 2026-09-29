-- Prove2me | Theorems.Thm_LocalSearchFL_MultiSwap_exists_partition_claim_3_1
-- name    : LocalSearchFL.MultiSwap.exists_partition_claim_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:39:19.380373+00:00
-- url     : https://prove2.me/theorems/81d1cc27-122a-4666-bc1b-32c1c6801345
-- title:
--   Claim 3.1 — partition of S and O into blocks with B_i = capture(A_i)
-- statement:
--   Let $S$ and $O$ be two sets of facilities with $|S| = |O|$, and let $\sigma_S, \sigma_O$ be client assignments; capture, good and bad are as defined for $S$ and $O$. Then there are an integer $r \ge 1$, a partition of $S$ into $A_1, \dots, A_r$ and a partition of $O$ into $B_1, \dots, B_r$ such that
--
--   1. for $1 \le i \le r-1$, $|A_i| = |B_i|$ and $B_i = \mathrm{capture}(A_i)$; and $|A_r| = |B_r|$;
--   2. for $1 \le i \le r-1$, the set $A_i$ has exactly one bad facility;
--   3. the set $A_r$ contains only good facilities.
--
--   The paper obtains the partition by the procedure of its Figure 8 and proves in Claim 3.1 that the procedure terminates with such partitions. The partition is the skeleton of the swaps used in the $p$-swap analysis.
--
--   **Formalization Note** The claim is stated in existence form: the procedure itself is not formalized. The blocks $A_1,\dots,A_{r-1}$ are a family indexed by `Fin m` ($r = m+1$) and $A_r$, $B_r$ are separate sets, which may be empty (as the procedure allows). "Partition" is stated as: every block is contained in $S$ (resp. $O$), the blocks are pairwise disjoint and cover $S$ (resp. $O$). Capture and goodness are computed against the original $S$ and $O$; since disjoint sets have disjoint captures, this gives the same blocks as the procedure's shrinking $O$.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, pp. 551–552, §3.4, Claim 3.1 and Figure 8

import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_capture

namespace LocalSearchFL.MultiSwap

/-- Claim 3.1 (p. 552), in existence form. If `|S| = |O|`, then `S` can be partitioned into
`A_1, …, A_r` and `O` into `B_1, …, B_r` (here `r = m + 1`, `A_i = A (i-1)` and `B_i = B (i-1)`
for `i ≤ m`, and `A_r = Ar`, `B_r = Br`) such that
1. for `1 ≤ i ≤ r − 1`, `|A_i| = |B_i|` and `B_i = capture(A_i)`; and `|A_r| = |B_r|`;
2. for `1 ≤ i ≤ r − 1`, `A_i` has exactly one bad facility;
3. `A_r` contains only good facilities.
Capture, good and bad are taken with respect to the original `S` and `O` (the assignments `σS`,
`σO` and the set `O`). The last blocks `Ar`, `Br` may be empty. -/
theorem exists_partition_claim_3_1 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) :
    ∃ (m : ℕ) (A B : Fin m → Finset Fa) (Ar Br : Finset Fa),
      -- `A_1, …, A_{r-1}, A_r` partition `S`
      (∀ i, A i ⊆ S) ∧ Ar ⊆ S ∧ (∀ s ∈ S, (∃ i, s ∈ A i) ∨ s ∈ Ar) ∧
      (∀ i i', i ≠ i' → Disjoint (A i) (A i')) ∧ (∀ i, Disjoint (A i) Ar) ∧
      -- `B_1, …, B_{r-1}, B_r` partition `O`
      (∀ i, B i ⊆ O) ∧ Br ⊆ O ∧ (∀ o ∈ O, (∃ i, o ∈ B i) ∨ o ∈ Br) ∧
      (∀ i i', i ≠ i' → Disjoint (B i) (B i')) ∧ (∀ i, Disjoint (B i) Br) ∧
      -- property 1
      (∀ i, (A i).card = (B i).card ∧ B i = capture σS σO O (A i)) ∧ Ar.card = Br.card ∧
      -- property 2
      (∀ i, ∃ b ∈ A i, ¬ IsGood σS σO O b ∧ ∀ s ∈ A i, s ≠ b → IsGood σS σO O s) ∧
      -- property 3
      (∀ s ∈ Ar, IsGood σS σO O s) := by sorry

end LocalSearchFL.MultiSwap
