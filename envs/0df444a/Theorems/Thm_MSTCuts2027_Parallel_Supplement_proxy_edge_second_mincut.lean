-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_Supplement_proxy_edge_second_mincut
-- name    : MSTCuts2027.Parallel.Supplement.proxy_edge_second_mincut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:39:43.369302+00:00
-- url     : https://prove2.me/theorems/f999a7fa-cd80-4ca2-a03b-d0e16a66b576
-- title:
--   Lemma 10 — proxy edge for second mincuts from $x$ to $V_2$ in $O(|V_2|)$ time
-- statement:
--   There are a program and constants $c,k$ such that the following holds for every $n$, every symmetric real cut function $F$ on $n$ vertices for which every pair of distinct vertices has a second mincut, and the machine with word size $(n+2)^k$. Let $V_2$ be a set of vertices, listed in memory, and $x\notin V_2$ a vertex such that for all distinct $u,v\in V_2$
--   $$\lambda_1(u,v)\ge\lambda_1(x,u)=\lambda_1(x,v).$$
--   Let $T_2$ be any MST of $G_2[V_2]$. Let the memory hold, for every ordered pair of distinct vertices of $V_2$, a pointer to a mincut with its value $\lambda_1$ and a pointer to a second mincut, and the values $\lambda_1(x,v)$ for $v\in V_2$; let $\mathcal C_2$ be the set of cuts these pointers point to. Then the program halts with work at most $c\,|V_2|$ and reports a vertex $a\in V_2$ such that, writing $e_p(x,T_2)=(x,a)$:
--
--   1. for every $v\in V_2$, either $\mathcal C_2$ contains a second $(x,v)$-mincut, or every second $(x,a)$-mincut is a second $(x,v)$-mincut;
--   2. $(x,a)$ has maximum capacity among the edges $\{(x,v): v\in V_2\}$ of $G_2$:
--   $$\lambda_2(x,v)\le\lambda_2(x,a)\quad\text{for all } v\in V_2.$$
--
--   This generalizes the proxy edge of Lemma 6 to second mincuts: one second-mincut computation for $(x,a)$, together with $\mathcal C_2$, gives a second mincut for every pair $(x,v)$, $v\in V_2$.
--
--   Differences from the source:
--   - encoding: there exists an algorithm running in O(|V2|) time → there exist one program and constants c, k fixed before the instance, with work at most c·|V2| on the machine of word size (n+2)^k; reason: the paper gives no numerical constant; the program may depend on nothing in the instance
--   - encoding: C2 a set of cuts consisting of a mincut cover and a second mincut cover of V2 × V2 → the cuts pointed to by the stored tables M and M2 for the ordered pairs of distinct vertices of V2; reason: this is the cut store of Appendix D and E; the stored set may contain more cuts than needed
--   - reading: the algorithm's input → also the values λ1(u,v) for u, v ∈ V2 (with M) and λ1(x,v) for v ∈ V2 in real cells; reason: the type test of Algorithm 5 (lines 2 and 4) reads these values, which in the paper's setting are known from the all-pairs mincuts computed first (§5.4); a cut function cannot be evaluated in the machine
--   - encoding: pairs (u,v) ∈ V2 → pairs of distinct vertices of V2; reason: λ1 is defined only on pairs of distinct vertices
--   - encoding: the edge ep(x,T2) → the vertex a written to an output cell, with the edge (x,a); reason: the edge is determined by a
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 10, printed p. 13, PDF p. 15

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondCutModel
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondAlgorithms

namespace MSTCuts2027.Parallel.Supplement

open MSTCuts2027.Parallel

/-- Lemma 10 (Proxy Edge for 2nd Mincut): one fixed program reports, in `O(|V₂|)` work, a vertex
`a` such that `(x, a)` is a proxy edge for second mincuts from `x` to `V₂` for the stored
mincut and second-mincut covers of `V₂`. The list `L` is any listing of `V₂` in the array
`ord`, the result is written to `dest`. -/
theorem proxy_edge_second_mincut :
    ∃ (A : Program) (entry c k : ℕ), ∀ (n : ℕ) (F : Finset (Fin n) → ℝ),
      IsSymmetricCutFunction F → SecondMincutsExist F →
      ∀ (P : Oracle ℝ n) (σ : Store ℝ) (l : ℕ) (L : List (Fin n)) (x : Fin n) (dest : ℕ)
        (T₂ : SimpleGraph {y // y ∈ L.toFinset}),
        IsReady n σ → OrdOK σ l L → TableOK F σ L.toFinset → Table2OK F σ L.toFinset →
        LamRowOK F σ x L.toFinset → dest ≤ wordBound n →
        IsMST2On F L.toFinset T₂ → x ∉ L →
        (∀ u ∈ L, ∀ v ∈ L, u ≠ v → lam F x u ≤ lam F u v ∧ lam F x u = lam F x v) →
        ∃ o : Outcome ℝ,
          Halts (⟨(n + 2) ^ k, P⟩ : Machine ℝ n) A entry
            [((x : ℕ) : ℤ), (l : ℤ), (L.length : ℤ), (dest : ℤ)] σ o ∧
          o.work ≤ c * L.length ∧
          ∃ a : Fin n, o.store.mem dest = ((a : ℕ) : ℤ) ∧
            IsProxyEdge2 F x L.toFinset
              (storedCover σ L.toFinset ∪ storedCover2 σ L.toFinset) a := by sorry

end MSTCuts2027.Parallel.Supplement
