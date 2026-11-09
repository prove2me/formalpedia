-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_dac_assign_mincut
-- name    : MSTCuts2027.Parallel.dac_assign_mincut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:39.341079+00:00
-- url     : https://prove2.me/theorems/8c21e265-bb93-40d1-a55e-4a7e013bddb7
-- title:
--   Lemma 13 — DACAssignMincut assigns all pointers of $x$ in $O(|B|)$ time
-- statement:
--   There is a constant $c$ such that for every symmetric real cut function $F$: let $B$ be a set of vertices with an MST $T_B$ of $G_1[B]$, let the pointer array hold correct pointers and values on $B$, let $x\notin B$, let memory hold the recursion tree $T(x)$ with root edge $(x,a)$, and let $M(x,a)$ and $M(a,x)$ hold a correct pointer and value. Then DACAssignMincut for $x$ halts with
--   $$\text{work}\le c|B|,\qquad \text{depth}\le c(\lceil\log_2|B|\rceil+1),$$
--   and afterwards all pairs of $B\cup\{x\}$ have a correct pointer and value.
--
--   Differences from the source:
--   - encoding: O(·) time bound → explicit constant c fixed before the instance, bounding the work (and depth where stated) of a machine run; reason: the paper gives no numerical constant; c may depend only on the fixed program
--   - reading: given a proxy edge, T(x) and the pointers {M(u, v) | u, v ∈ B} → also given that M(x, a) and M(a, x) hold the mincut pointer of the proxy edge and its value, and the values of the pairs of B; reason: Appendix D, printed p. 22, states these facts as holding when the routine is called; without the cut of the proxy edge the statement would be false
--   - encoding: compute {M(x, y) | y ∈ B} → afterwards TableOK holds on B ∪ {x}: M(x, y), M(y, x) and the values are correct, and the entries of B persist; reason: M is a matrix over all pairs, and Algorithm 4 needs the invariant of Appendix D
--   - encoding: any set of vertices → a duplicate-free list L in the array ord at positions l, …; reason: every finite set has such a listing, so no instance is lost; the list gives the machine random access to the set
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 13, printed p. 22, PDF p. 24

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- Lemma 13: given the proxy edge `(x, a)` with its pointer, the tree `T(x)` and the pointers inside
`B`, the program fills `M(x, y)` and `M(y, x)` for all `y ∈ B` in `O(|B|)` work. -/
theorem dac_assign_mincut :
    ∃ c : ℕ, ∀ (n : ℕ) (F : Finset (Fin n) → ℝ), IsSymmetricCutFunction F →
      ∀ (P : Oracle ℝ n) (σ : Store ℝ) (l : ℕ) (L : List (Fin n)) (x a : Fin n)
        (T : SimpleGraph {y // y ∈ L.toFinset}),
        IsReady n σ → L.Nodup → l + L.length ≤ n → TableOK F σ L.toFinset →
        IsMSTOn F L.toFinset T → x ∉ L →
        IsRecursionTree σ.mem x l L →
        σ.mem (treeAddr n x l (Nat.clog 2 L.length) 0) = ((a : ℕ) : ℤ) →
        EntryOK F σ x a → EntryOK F σ a x →
        ∃ o : Outcome ℝ,
          Halts (machine P) algorithms Prog.pAssignLoop
            [((x : ℕ) : ℤ), (l : ℤ), 0, (L.length : ℤ)] σ o ∧
          o.work ≤ c * L.length ∧ o.depth ≤ c * (Nat.clog 2 L.length + 1) ∧
          TableOK F o.store (insert x L.toFinset) := by sorry

end MSTCuts2027.Parallel
