-- Prove2me | Theorems.Thm_IntervalExplore_KT1_Supplement_theorem_3
-- name    : IntervalExplore.KT1.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:02:19.116204+00:00
-- url     : https://prove2.me/theorems/7408f3a3-45e6-489d-9ed0-14f88a4c6325
-- title:
--   Theorem 3 — the minimum window $\psi_k(n,m)$ is $\Omega(m)$ in KT0 and KT1
-- statement:
--   For $k\in\{0,1\}$, $n\ge3$ and $m\in[n..\binom n2]$, let $\psi_k(n,m)$ be the least window $T$ for which some deterministic KT$_k$ algorithm explores every $T$-interval-connected graph with $n$ nodes and $m$ edges (Definition 1). The theorem says $\psi_k(n,m)=\Omega(m)$. Stated without $\psi_k$: there are $c>0$ and $N$ such that for all $n\ge N$, all $m$ with $n\le m\le\binom n2$ and every window $T$ with
--   $$
--   1\le T\le c\,m ,
--   $$
--   1. every deterministic KT0 algorithm, and
--   2. every deterministic KT1 algorithm
--
--   has an instance (a graph on $n$ nodes with exactly $m$ underlying edges, a $T$-interval-connected schedule, identifiers, ports and a starting node) on which some node is never visited. In particular no KT$_k$ algorithm explores all such instances, so $\psi_k(n,m)>c\,m$.
--
--   Together with Corollary 1 this determines the minimum window up to the factor $\xi(n,m)+(n\log^2 n)/m$, and gives $\psi_k(n)=\Theta(n^2)$.
--
--   **Formalization Note** Edges of the underlying graph that never appear (null edges) count towards $m$. The first clause follows from the second, since every KT0 algorithm is a KT1 algorithm; both are stated, as the source does.
--
--   Differences from the source:
--   - generalization: ψ_k(n,m) ≥ c·m, i.e. every KT_k algorithm fails to explore (visit all nodes and terminate) some T-interval-connected instance for each T < c·m → for each T with 1 ≤ T ≤ c·m every algorithm has an instance where some node is never visited at any time; reason: never visiting a node implies not exploring, and T ≤ c·m covers every T < c·m; this is what the proof (pp.14–15) shows
--   - encoding: ψ_k(n,m) = Ω(m) → ∃c>0, ∃N, ∀n ≥ N, ∀m ∈ [n..C(n,2)], fixed before every algorithm and window; reason: the asymptotic statement with absolute constants; ψ_k is not defined as a minimum since the lower bound needs only the failure of every smaller window
--   - encoding: a graph with n nodes → vertex type Fin n; reason: identifiers are separate data, so every n-node instance is isomorphic to one on Fin n
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Theorem 3, p.4 (PDF p.5), with Definition 1, p.4 (PDF p.5); proof pp.14–15 (PDF pp.15–16)

import Definitions.Def_IntervalExplore_KT1_Supplement_Model

set_option autoImplicit false

namespace IntervalExplore.KT1.Supplement

open IntervalExplore.KT1

/-- Theorem 3, p.4 (PDF p.5): ψ_k(n,m) = Ω(m) for k ∈ {0,1}. For every window T with
1 ≤ T ≤ c·m, every KT0 algorithm (first clause) and every KT1 algorithm (second clause)
has a T-interval-connected instance with n nodes and m edges on which some node is never
visited; hence ψ_k(n,m) > c·m. -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ, n ≤ m → m ≤ n.choose 2 →
      ∀ T : ℕ, 1 ≤ T → (T : ℝ) ≤ c * m →
        (∀ A : Alg, IsKT0 A → ∃ W : World (Fin n), edgeCount W.graph = m ∧
            IntervalConnected W.dynamic T ∧
            ∃ v : Fin n, ∀ t : ℕ, (state W A t).position ≠ v) ∧
        (∀ A : Alg, ∃ W : World (Fin n), edgeCount W.graph = m ∧
            IntervalConnected W.dynamic T ∧
            ∃ v : Fin n, ∀ t : ℕ, (state W A t).position ≠ v) := by sorry

end IntervalExplore.KT1.Supplement
