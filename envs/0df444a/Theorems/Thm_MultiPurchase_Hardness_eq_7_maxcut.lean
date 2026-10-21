-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_eq_7_maxcut
-- name    : MultiPurchase.Hardness.eq_7_maxcut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:03.913561+00:00
-- url     : https://prove2.me/theorems/321b1239-b33f-49fa-8879-acfbdfe6a1ed
-- title:
--   Proof of Theorem 1, App. pp. 4–5 — problem (7) with Q = (0, d/2; d/2, −A′) is Max-Cut on G
-- statement:
--   Let $G$ be a simple graph on the nodes $\{1,\dots,m\}$ with degree vector $\mathbf d=(d_1,\dots,d_m)$ and adjacency matrix $A'$, and let $Q=(q_{ij})_{0\le i,j\le m}$ be the matrix
--   $$Q=\begin{pmatrix}0&\mathbf d^\top/2\\ \mathbf d/2&-A'\end{pmatrix},$$
--   indexed from $0$. For $C\subseteq\{0,1,\dots,m\}$ write $f(C)=\sum_{0\le i\le m}\sum_{0\le j\le m}q_{ij}x^C_ix^C_j$ for the objective of problem (7), and $\tilde C=C\setminus\{0\}$. Then:
--   1. $f(C)\le f(C\cup\{0\})$ for every $C$, so an optimal solution of (7) may take $x^{C}_0=1$;
--   2. if $0\in C$, then $f(C)$ equals the number of edges of $G$ across the cut $(\tilde C,\{1,\dots,m\}\setminus\tilde C)$;
--   3. consequently, for every natural number $M$, some $C$ has $f(C)\ge M$ if and only if $G$ has a cut with at least $M$ edges.
--
--   This identifies the quadratic program (7) with the Max-Cut problem on $G$; it is the combinatorial core of the hardness proof.
--
--   **Formalization Note** The hub is index `0 : Fin (m+1)` and node $i$ of the graph is index `i.succ`; $\tilde C$ is the set of nodes $i$ with `i.succ ∈ C`. Since $G$ is a simple graph, $G'=G$. The cut size counts each edge once.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, proof of Theorem 1, Appendix pp. 4–5 (PDF 36–37), matrix Q, problem (7) and the display following it

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

open ProjSchedTW.Complexity

/-- Proof of Theorem 1, Appendix pp. 4–5: problem (7), `max_{C∈2^W} ∑_{0≤i≤m} ∑_{0≤j≤m}
qᵢⱼ x^C_i x^C_j` for `Q = (0, d/2; d/2, −A′)`, is the Max-Cut problem on `G`.
(1) Adding the hub `0` never decreases the objective, so an optimum may take `x^C_0 = 1`;
(2) when `0 ∈ C` the objective equals the number of edges across the cut `(C̃, {1,…,m} ∖ C̃)`,
`C̃ = C ∖ {0}`; (3) hence the objective reaches `M` for some `C` iff `G` has a cut of size
at least `M`. -/
theorem eq_7_maxcut {m : ℕ} (G : SimpleGraph (Fin m)) :
    (∀ C : Finset (Fin (m + 1)),
      ∑ i, ∑ j, hubQ G i j * xC C i * xC C j ≤
        ∑ i, ∑ j, hubQ G i j * xC (insert 0 C) i * xC (insert 0 C) j) ∧
    (∀ C : Finset (Fin (m + 1)), 0 ∈ C →
      ∑ i, ∑ j, hubQ G i j * xC C i * xC C j = (cutSize G (nodesOf C) : ℚ)) ∧
    (∀ M : ℕ, (∃ C : Finset (Fin (m + 1)), (M : ℚ) ≤ ∑ i, ∑ j, hubQ G i j * xC C i * xC C j) ↔
      MaxCutYes G M) := by sorry

end MultiPurchase.Hardness
