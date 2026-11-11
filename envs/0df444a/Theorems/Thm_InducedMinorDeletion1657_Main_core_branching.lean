-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_core_branching
-- name    : InducedMinorDeletion1657.Main.core_branching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:53.282989+00:00
-- url     : https://prove2.me/theorems/2d095886-3633-4216-9930-fa14962e333a
-- title:
--   Lemma 4.2 — core branching (corrected: t=1 logarithm)
-- statement:
--   For any graph $G$ and positive integers $k,d,t$ with $d>2t$, compute pairs $(X_i,M_i)$ with count at most $C(k+2)^{C(t+1)^ak/d}$ and time at most that quantity times $(n+1)^c$. The constants and program are uniform in all these inputs. Each pair satisfies
--   $$\operatorname{tw}(G-(X_i\cup M_i))\le t,\qquad |M_i|\le Ct^2\log_2\max(2,t)\,k.$$
--   The set $M_i$ is a $C(d+t)$-core in $G-X_i$, and $G[M_i]$ is $d$-degenerate. Every treewidth-$t$ modulator $S$ of size at most $k$ contains some $X_i$. All guarantees concern the same collection and pairs; no modulator is an input. This is the full four-clause interface of Algorithm 1.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite published register program, actual halting iteration, output charge and logarithmically bounded words; reason: operational word-RAM reading; constants and the program precede every varying graph and numerical input
--   - encoding: O notation and small input bases n, k → positive uniform constants, n+1 and k+2, and an upper bound on collection size; reason: makes source asymptotics pointwise at small inputs without changing any unbounded parameter dependence
--   - correction: O(t² log t · k) at t = 1 → O(t² log₂(max(2,t)) · k); reason: k disjoint triangles, d=k² force 3^k distinct X outputs if every M is empty, contradicting the stated k^{O(k/d)} count
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 16 (PDF p. 17), Lemma 4.2; clause (iv) continues p. 17 (PDF p. 18)

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 4.2, printed p. 16 / PDF p. 17. See the local source audit for conventions. -/
theorem core_branching :
∃ (P : Program) (C a c q : ℕ), 0 < C ∧ 0 < a ∧ 0 < c ∧ 0 < q ∧
  ∀ (G : InputGraph) (k d t : ℕ), 0 < k → 0 < t → 2*t < d →
    ∃ Q : List (Finset (Fin G.n) × Finset (Fin G.n)),
      coreBranchResult G k d t C Q ∧
      (Q.length : ℝ) ≤ branchCount C a k d t ∧
      ramOutputs P (k :: d :: t :: graphWords G) (pairWords Q)
        (branchTime C a c G.n k d t) q := by sorry

end InducedMinorDeletion1657.Main
