-- Prove2me | Theorems.Thm_GuardedSSSP_Supplement_theorem_C_1
-- name    : GuardedSSSP.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:22:17.811219+00:00
-- url     : https://prove2.me/theorems/e4302ffa-a1a8-4b24-b168-0c2bed4eddd3
-- title:
--   Theorem C.1, p.37 — reusable seeded queries: $O((m+n)\alpha(m+n+2)+h\log_2(h+1))$ time and $O(m+n+h\log_2(h+1))$ additions and comparisons per query
-- statement:
--   Let $H$ be a finite directed multigraph with $n\ge1$ vertices, $m$ arcs and fixed nonnegative real weights $w$. Choose a root $r$ reaching every vertex, let $p(v)=\mathrm{dist}_H(r,v)$, and let the dominator tree of $(H,r)$ have $h$ leaves. Then there is a deterministic preprocessing and query algorithm on the comparison–addition RAM such that, with $T_{\mathrm{dom}}$ and $T_{\mathrm{cal}}$ the costs of computing the dominator tree and $p$,
--
--   $$T_{\mathrm{prep}}=O(T_{\mathrm{dom}}+T_{\mathrm{cal}}+m+n),\qquad T_{\mathrm{query}}=O\big((m+n)\,\alpha(m+n+2)+h\log_2(h+1)\big),$$
--
--   $$\mathrm{CA}_{\mathrm{query}}=O\big(m+n+h\log_2(h+1)\big),$$
--
--   and every query, for an arbitrary seed vector $\beta:V\to[0,\infty]$, returns all values $d_\beta(v)=\min_x\{\beta(x)+\mathrm{dist}_H(x,v)\}$ (44) as held scalars or infinity tags. Prepared storage and query workspace are $O(m+n)$, and the bounds include reading the seeds, initializing the query state and writing all outputs. Here $\mathrm{CA}_{\mathrm{query}}$ counts real additions and comparisons and $\alpha$ is an inverse-Ackermann function.
--
--   Precisely: there are two programs $\mathrm{Prep}$, $\mathrm{Query}$ of the base mission's RAM and a constant $C>0$ such that for every instance, $\mathrm{Prep}$, given $(H,w,r)$ together with the dominator tree and $p$, halts within $C(m+n)$ steps writing at most $C(m+n)$ cells; and for every seed vector, $\mathrm{Query}$, started from $\mathrm{Prep}$'s final memory with the seeds written in, halts within $C((m+n)\alpha(m+n+2)+h\log_2(h+1))$ steps, executes at most $C(m+n+h\log_2(h+1))$ real additions and comparisons, writes at most $C(m+n)$ cells, and outputs $d_\beta$ exactly.
--
--   The theorem lets a fixed weighted graph answer arbitrarily many seeded shortest-path queries, each in near-linear time with a numerical cost governed by the number of leaves of the dominator tree.
--
--   **Formalization Note** Layouts: `GuardedSSSP.Supplement.prepInit`, `queryInit`, `SeededOutputCorrect`; measures: `haltTime`, `numCA`, `space`. Each query restarts from the prepared memory, so seeds chosen after earlier answers are covered.
--
--   Differences from the source:
--   - reading: a deterministic preprocessing and query algorithm in the comparison–addition RAM of Appendix D → two programs Prep, Query of the base mission's comparison–addition RAM (GuardedSSSP.Machine), each with word bound (m + n + 2)^c for its own c; reason: Appendix D's RAM is the base mission's §4.1 model (same instructions, unit cost, no real literal but 0, no casts)
--   - reading: T_prep = O(T_dom + T_cal + m + n) (45), and O(P_cal + m + n) numerical operations in addition to the topology-only tree construction → Prep receives the dominator-tree parent array and the exact p = dist_H(r, ·) as input and halts within C(m + n) steps; reason: T_dom and T_cal are the costs of whatever algorithms compute the tree and p; running them first and then Prep gives (45) and the P_cal clause for every such choice
--   - reading: O(·) in (45)–(47) and in the storage bounds → one constant C > 0 chosen with the programs, before every graph, root, weighting and seed vector; reason: the theorem asserts one algorithm with absolute constants
--   - reading: prepared storage and query workspace are both O(m + n) → the distinct memory cells written by Prep, and by each query run, number at most C(m + n); reason: the input itself occupies O(m + n) cells and a program uses a fixed set of registers
--   - reading: α, a standard one-parameter inverse-Ackermann upper bound for union by rank with path compression → Algo2Lean.Ackermann.alpha (least k > 0 with m + n + 2 < A_k(1)) applied to m + n + 2; reason: the paper fixes no variant; standard one-parameter variants differ by O(1), which the factor (m + n) absorbs
--   - encoding: repeated queries on the fixed graph, seeds possibly depending on earlier answers → every query starts from Prep's final memory, registers reset, with the seeds written at cells −1 − v; the statement holds for every seed vector; reason: a statement for every seed vector from the same prepared memory covers every adaptive sequence of queries
--   - encoding: seeds β(v) ∈ [0, ∞] and outputs as held scalar registers or infinity tags → presence flag in integer cell −1 − v and value in real cell −1 − v, for seeds and for outputs (the base mission's output format); reason: the paper fixes no layout
--   - encoding: a root r reaching every vertex → dist_H(r, v) ≠ ⊤ for every v; reason: a vertex is reachable exactly when its walk distance is finite
--   - encoding: its dominator tree has h leaves → any parent map dpar with dpar r = r and dpar v = idom(v) for v ≠ r (IsDomTree), h = number of vertices with no child; reason: the dominator tree is unique, so quantifying over every such dpar is the same condition
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Theorem C.1, p.37 (PDF p.38); (44), p.36 (PDF p.37)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist
import Definitions.Def_GuardedSSSP_Machine
import Definitions.Def_GuardedSSSP_Dominates
import Definitions.Def_Algo2LeanLib_Ackermann
import Definitions.Def_GuardedSSSP_Supplement_seededDist
import Definitions.Def_GuardedSSSP_Supplement_RootedTree
import Definitions.Def_GuardedSSSP_Supplement_MachineRuns
import Definitions.Def_GuardedSSSP_Supplement_SeededQueryLayout

namespace GuardedSSSP

namespace Supplement

open AtomicDynRouting.ResidenceTime GuardedSSSP.Machine

/-- **Theorem C.1** (Reusable seeded queries).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), Theorem C.1, p.37 (PDF p.38), with (44), p.36 (PDF p.37).

"Let H be a finite directed multigraph with n ≥ 1 vertices, m arcs and fixed nonnegative real weights.
Choose a root r reaching every vertex, and let its dominator tree have h leaves. Let T_dom and T_cal be the
actual RAM costs of computing that tree and the scalar distances p(v) = dist_H(r, v), respectively. There
is a deterministic preprocessing and query algorithm with T_prep = O(T_dom + T_cal + m + n) (45),
T_query = O((m + n)α(m + n + 2) + h log₂(h + 1)) (46), CA_query = O(m + n + h log₂(h + 1)) (47). Every query
returns all values in (44) as held scalar registers or infinity tags. Prepared storage and query workspace
are both O(m + n). These bounds include reading the seeds, initializing the query state, and writing all
outputs. If calibration uses P_cal additions and comparisons, preprocessing uses O(P_cal + m + n) numerical
operations in addition to the topology-only tree construction."

There are two programs `Prep`, `Query` of the base comparison–addition RAM and one constant `C > 0` such
that for every `n`, `m`, multigraph `G`, weights `w ≥ 0`, root `r` reaching every vertex and dominator tree
`dpar` of `(G, r)` with `h` leaves:
1. `Prep`, started on `(G, r, w)` with `dpar` and `p = dist_G(r, ·)` supplied, halts within `C(m + n)`
   steps and writes at most `C(m + n)` distinct memory cells;
2. for every seed vector (presence flags and nonnegative values), `Query`, started from the prepared memory
   with the seeds written in, halts within `C((m + n)α(m + n + 2) + h log₂(h + 1))` steps, executes at most
   `C(m + n + h log₂(h + 1))` real additions and comparisons, writes at most `C(m + n)` distinct memory
   cells, and leaves `d_β(v)` (44) with infinity tags in the output cells.

**Formalization Note.**
* The machine is the base mission's `GuardedSSSP.Machine` (two banks, unit cost, no real literal but `0`,
  no real multiplication, no casts); each program's word bound is `(m + n + 2)^c` with `c` its own
  `wordExp`. `C` is chosen before the instance.
* (45) and the `P_cal` clause: the dominator tree and the calibration are supplied to `Prep` (layout in
  `prepInit`), and `Prep` must then halt within `C(m + n)` steps; running any tree algorithm (cost
  `T_dom`) and any calibration algorithm (cost `T_cal`, `P_cal` numerical operations) before it gives
  `T_prep ≤ T_dom + T_cal + C(m + n)` and at most `P_cal + C(m + n)` numerical operations.
* Each query starts from `Prep`'s final memory (`queryInit`), so the statement covers any number of queries
  with seeds chosen after earlier answers.
* Storage and workspace: the number of distinct cells written by `Prep`, and by each query run, is at most
  `C(m + n)` (the input itself occupies `O(m + n)` cells).
* `α` is `Algo2Lean.Ackermann.alpha` (least `k > 0` with `m + n + 2 < A_k(1)`); `log₂` is `Real.logb 2`.
* `n ≥ 1` holds because `r : Fin n`. -/
theorem theorem_C_1 :
    ∃ (Prep Query : Program) (C : ℝ), 0 < C ∧
      ∀ {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ), (∀ e, 0 ≤ w e) →
        ∀ r : Fin n, (∀ v, dist G w r v ≠ ⊤) →
          ∀ dpar : Fin n → Fin n, IsDomTree G r dpar →
            Halts Prep (wordBound Prep n m)
                (prepInit G r w dpar (fun v => (dist G w r v).toReal)) ∧
            (haltTime Prep (wordBound Prep n m)
                (prepInit G r w dpar (fun v => (dist G w r v).toReal)) : ℝ) ≤ C * (m + n) ∧
            (space Prep (wordBound Prep n m)
                (prepInit G r w dpar (fun v => (dist G w r v).toReal)) : ℝ) ≤ C * (m + n) ∧
            ∀ (flag : Fin n → Bool) (val : Fin n → ℝ), (∀ v, flag v = true → 0 ≤ val v) →
              Halts Query (wordBound Query n m)
                  (queryInit (finalState Prep (wordBound Prep n m)
                    (prepInit G r w dpar (fun v => (dist G w r v).toReal))) flag val) ∧
              (haltTime Query (wordBound Query n m)
                  (queryInit (finalState Prep (wordBound Prep n m)
                    (prepInit G r w dpar (fun v => (dist G w r v).toReal))) flag val) : ℝ) ≤
                C * (((m + n : ℕ) : ℝ) * (Algo2Lean.Ackermann.alpha (m + n + 2) : ℝ) +
                  (numLeaves dpar r : ℝ) * Real.logb 2 ((numLeaves dpar r : ℝ) + 1)) ∧
              (numCA Query (wordBound Query n m)
                  (queryInit (finalState Prep (wordBound Prep n m)
                    (prepInit G r w dpar (fun v => (dist G w r v).toReal))) flag val) : ℝ) ≤
                C * ((m + n : ℝ) +
                  (numLeaves dpar r : ℝ) * Real.logb 2 ((numLeaves dpar r : ℝ) + 1)) ∧
              (space Query (wordBound Query n m)
                  (queryInit (finalState Prep (wordBound Prep n m)
                    (prepInit G r w dpar (fun v => (dist G w r v).toReal))) flag val) : ℝ) ≤
                C * (m + n) ∧
              SeededOutputCorrect G w (seedVec flag val)
                (finalState Query (wordBound Query n m)
                  (queryInit (finalState Prep (wordBound Prep n m)
                    (prepInit G r w dpar (fun v => (dist G w r v).toReal))) flag val)) := by sorry

end Supplement

end GuardedSSSP
