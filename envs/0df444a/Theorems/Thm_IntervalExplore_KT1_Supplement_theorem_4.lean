-- Prove2me | Theorems.Thm_IntervalExplore_KT1_Supplement_theorem_4
-- name    : IntervalExplore.KT1.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:02:58.48481+00:00
-- url     : https://prove2.me/theorems/7c2b3240-fb5f-4374-a581-909be31170ae
-- title:
--   Theorem 4 — KT0 exploration needs $\Omega((m-n+1)n)$ time on ∞-interval-connected graphs
-- statement:
--   There are $c>0$ and $N$ such that for every deterministic KT0 algorithm $A$, every $n\ge N$ and every $m$ with $n\le m\le\binom n2$, there is an ∞-interval-connected dynamic graph on $n$ nodes with exactly $m$ underlying edges, together with identifiers, ports and a starting node, such that for every time
--   $$
--   t<c\,(m-n+1)\,n
--   $$
--   some node has not been visited by the agent running $A$ during the steps $0,\dots,t$. In particular the agent cannot explore the graph (visit every node and terminate) in fewer than $c(m-n+1)n$ steps.
--
--   With Theorem 1 this gives the exploration time $\Theta((m-n+1)n)$ in KT0 whenever $m=n+\Omega(\log^2 n)$, and $\Theta(n^3)$ as a function of $n$ alone.
--
--   **Formalization Note** $c$ and $N$ are absolute and precede the algorithm; the instance depends on $A$. Null edges count towards $m$.
--
--   Differences from the source:
--   - generalization: "requires Ω((m−n+1)n) time to explore the graph" → before time c·(m−n+1)·n some node is still unvisited; reason: not having visited a node implies not having explored (visited every node and terminated); this is what the proof (pp.16–17) shows, and it excludes the trivial failure of a nonterminating algorithm
--   - reading: Ω(·) for every algorithm A and every sufficiently large n (the order of quantifiers leaves open whether the constant and the threshold may depend on A) → ∃c>0, ∃N, fixed before every algorithm; reason: the stronger, uniform reading; the proof's bound and threshold are independent of the algorithm
--   - encoding: a graph with n nodes → vertex type Fin n; reason: identifiers are separate data, so every n-node instance is isomorphic to one on Fin n
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Theorem 4, p.5 (PDF p.6); proof pp.16–17 (PDF pp.17–18)

import Definitions.Def_IntervalExplore_KT1_Supplement_Model

set_option autoImplicit false

namespace IntervalExplore.KT1.Supplement

open IntervalExplore.KT1

/-- Theorem 4, p.5 (PDF p.6): KT0 exploration-time lower bound Ω((m−n+1)n), with c and N
fixed before the algorithm. Before time c·(m−n+1)·n some node is still unvisited. -/
theorem theorem_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ A : Alg, IsKT0 A → ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, n ≤ m → m ≤ n.choose 2 →
        ∃ W : World (Fin n), edgeCount W.graph = m ∧ InfIntervalConnected W.dynamic ∧
          ∀ t : ℕ, (t : ℝ) < c * (((m : ℝ) - n + 1) * n) →
            ∃ v : Fin n, ∀ s ≤ t, (state W A s).position ≠ v := by sorry

end IntervalExplore.KT1.Supplement
