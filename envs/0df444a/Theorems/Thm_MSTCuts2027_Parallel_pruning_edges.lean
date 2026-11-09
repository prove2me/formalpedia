-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_pruning_edges
-- name    : MSTCuts2027.Parallel.pruning_edges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:29.961191+00:00
-- url     : https://prove2.me/theorems/673328cf-f12a-41bc-bcd8-1422101eda85
-- title:
--   Lemma 6 — a proxy edge from $x$ to $V_2$ in $O(|V_2|)$ time
-- statement:
--   There is a constant $c$ such that for every symmetric real cut function $F$: let $V_2$ be a set of vertices listed in the machine's array, let $T_2$ be any MST of $G_1[V_2]$, let the machine's pointer array hold a mincut cover $C_2$ for all pairs of $V_2$, and let $x\notin V_2$. Then the pruning program halts with work at most $c|V_2|$ and reports an edge $(x,a)$, $a\in V_2$, denoted $e_p(x,T_2)$, such that:
--
--   1. for every $v\in V_2$, either some cut of $C_2$ is an $(x,v)$-mincut, or every $(x,a)$-mincut is an $(x,v)$-mincut;
--   2. $(x,a)$ has maximum capacity among the edges $\{(x,v):v\in V_2\}$ of $G_1$.
--
--   So only one edge from $x$ to $V_2$ needs a new mincut computation.
--
--   Differences from the source:
--   - encoding: O(·) time bound → explicit constant c fixed before the instance, bounding the work (and depth where stated) of a machine run; reason: the paper gives no numerical constant; c may depend only on the fixed program
--   - encoding: any set of vertices → a duplicate-free list L in the array ord at positions l, …; reason: every finite set has such a listing, so no instance is lost; the list gives the machine random access to the set
--   - encoding: a mincut cover → the cuts that the pointer array M points to, stored as Boolean arrays in the cut store, with the mincut values in real cells; reason: Appendix E stores C and M this way; a cover can always be laid out so
--   - encoding: the algorithm eliminates edges in arbitrary pairs → the consecutive pairing of Algorithm 8; reason: the proof of Lemma 6 picks any two edges at each step, so this is one of its executions
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 6, printed p. 7, PDF p. 9

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- Lemma 6: from a stored cover of `V₂` the proxy edge of `x` is found in `O(|V₂|)` work. The list
`L` is any listing of `V₂` in the array `ord`. -/
theorem pruning_edges :
    ∃ c : ℕ, ∀ (n : ℕ) (F : Finset (Fin n) → ℝ), IsSymmetricCutFunction F →
      ∀ (P : Oracle ℝ n) (σ : Store ℝ) (l : ℕ) (L : List (Fin n)) (x : Fin n)
        (T : SimpleGraph {y // y ∈ L.toFinset}),
        IsReady n σ → OrdOK σ l L → TableOK F σ L.toFinset → IsMSTOn F L.toFinset T → x ∉ L →
        ∃ o : Outcome ℝ,
          Halts (machine P) algorithms Prog.pPruneOne
            [((x : ℕ) : ℤ), (l : ℤ), (L.length : ℤ)] σ o ∧
          o.work ≤ c * L.length ∧
          ∃ a : Fin n, rootValue n o.store.mem x l = ((a : ℕ) : ℤ) ∧
            IsProxyEdge F x L.toFinset (storedCover σ L.toFinset) a := by sorry

end MSTCuts2027.Parallel
