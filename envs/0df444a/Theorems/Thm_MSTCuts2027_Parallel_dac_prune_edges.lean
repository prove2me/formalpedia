-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_dac_prune_edges
-- name    : MSTCuts2027.Parallel.dac_prune_edges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:06.379634+00:00
-- url     : https://prove2.me/theorems/724d44a1-a37d-4990-993e-71a200492814
-- title:
--   Lemma 12 — balanced recursive pruning
-- statement:
--   There is a constant $c$ such that for every symmetric real cut function $F$: let $B$ be a nonempty set of vertices listed in the machine's array, let the pointer array hold a mincut cover for all pairs of $B$, and let $x\notin B$. Algorithm 8 for $x$ halts with
--   $$\text{work}\le c|B|,\qquad \text{depth}\le c(\lceil\log_2|B|\rceil+1),$$
--   performs exactly $\lceil\log_2|B|\rceil$ rounds, leaves the recursion tree $T(x)$ in memory, and reports a proxy edge from $x$ to $B$ with the two properties of Lemma 6.
--
--   Differences from the source:
--   - encoding: O(·) time bound → explicit constant c fixed before the instance, bounding the work (and depth where stated) of a machine run; reason: the paper gives no numerical constant; c may depend only on the fixed program
--   - encoding: any set of vertices → a duplicate-free list L in the array ord at positions l, …; reason: every finite set has such a listing, so no instance is lost; the list gives the machine random access to the set
--   - encoding: a mincut cover → the cuts that the pointer array M points to, stored as Boolean arrays in the cut store, with the mincut values in real cells; reason: Appendix E stores C and M this way; a cover can always be laid out so
--   - encoding: O(log |B|) recursive depth → exactly ⌈log₂ |B|⌉ rounds, and depth at most c(⌈log₂ |B|⌉ + 1), the +1 covering |B| = 1; reason: log 1 = 0 while a run takes at least one step; the O notation of the source covers this
--   - reading: can compute a proxy edge → the reported edge has the two properties of Lemma 6, and the tree T(x) is left in memory; reason: Appendix D defines the proxy edge by Lemma 6 and T(x) as the tree of this computation
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 12, printed p. 21, PDF p. 23

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- Lemma 12: Algorithm 8 for one vertex has `⌈log₂ |B|⌉` rounds and `O(|B|)` work, and reports a
proxy edge. The block `B` is listed by `L`. -/
theorem dac_prune_edges :
    ∃ c : ℕ, ∀ (n : ℕ) (F : Finset (Fin n) → ℝ), IsSymmetricCutFunction F →
      ∀ (P : Oracle ℝ n) (σ : Store ℝ) (l : ℕ) (L : List (Fin n)) (x : Fin n),
        IsReady n σ → L ≠ [] → OrdOK σ l L → TableOK F σ L.toFinset → x ∉ L →
        ∃ o : Outcome ℝ,
          Halts (machine P) algorithms Prog.pPruneOne
            [((x : ℕ) : ℤ), (l : ℤ), (L.length : ℤ)] σ o ∧
          o.work ≤ c * L.length ∧ o.depth ≤ c * (Nat.clog 2 L.length + 1) ∧
          o.store.mem (roundsAddr n x l) = (Nat.clog 2 L.length : ℤ) ∧
          IsRecursionTree o.store.mem x l L ∧
          ∃ a : Fin n, rootValue n o.store.mem x l = ((a : ℕ) : ℤ) ∧
            IsProxyEdge F x L.toFinset (storedCover σ L.toFinset) a := by sorry

end MSTCuts2027.Parallel
